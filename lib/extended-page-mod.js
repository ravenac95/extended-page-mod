/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
"use strict";

module.metadata = {
  "stability": "stable"
};

//const observers = require('sdk/deprecated/observer-service');
var events = require("sdk/system/events");
const unload = require('sdk/system/unload');
const { validationAttributes } = require('sdk/content/loader');
const { Worker } = require('sdk/content/worker');
const { MatchPattern } = require('sdk/util/match-pattern');
const { validateOptions : validate } = require('sdk/deprecated/api-utils');
const { Cc, Ci } = require('chrome');
const { merge } = require('sdk/util/object');
const { readURISync } = require('sdk/net/url');
const { windowIterator } = require('sdk/deprecated/window-utils');
const { isBrowser, getFrames } = require('sdk/window/utils');
const { getTabs, getTabContentWindow, getTabForContentWindow,
  getURI: getTabURI } = require('sdk/tabs/utils');
const { has, hasAny } = require('sdk/util/array');
const { ignoreWindow } = require('sdk/private-browsing/utils');
const { emit, count } = require('sdk/event/core');
const { EventTarget } = require('sdk/event/target');
const { Class } = require('sdk/core/heritage');
const { Disposable } = require('sdk/core/disposable');
const styleSheetService = Cc["@mozilla.org/content/style-sheet-service;1"].
  getService(Ci.nsIStyleSheetService);

const USER_SHEET = styleSheetService.USER_SHEET;

const io = Cc['@mozilla.org/network/io-service;1'].
  getService(Ci.nsIIOService);

// Valid values for `attachTo` option
const VALID_ATTACHTO_OPTIONS = ['existing', 'top', 'frame'];

// contentStyle* / contentScript* are sharing the same validation constraints,
// so they can be mostly reused, except for the messages.
const validStyleOptions = {
  contentStyle: merge(Object.create(validationAttributes.contentScript), {
    msg: 'The `contentStyle` option must be a string or an array of strings.'
  }),
  contentStyleFile: merge(Object.create(validationAttributes.contentScriptFile), {
    msg: 'The `contentStyleFile` option must be a local URL or an array of URLs'
  })
};

//const selfEmit = (event, data) => emit(this, event, data);
const selfEmit = function (event, data) {
  emit(this, event, data);
};

//@NOTE: Class should be replaced with proper es6 class Rules extends Map
/**
 * Maintains a mapping of URL to MatchPattern
 * @constructor
 */
const Rules = Class({
  implements: [EventTarget],
  initialize() {
    //We can't inherit from Map yet, so we're exposing what we need
    this._map = new Map();
  },
  add(rules) {
    [].concat(rules).forEach(rule => {
      if (this._map.has(rule)) return;

      this._map.set(rule, new MatchPattern(rule));
      this.emit('add', rule);
    });
  },
  remove(rules) {
    [].concat(rules).forEach(rule => {
      this._map.delete(rule);
      this.emit('remove', rule);
    });
  },
  emit: selfEmit,
  //@NOTE: Until we can properly extend Map
  values() {
    return this._map.values();
  },
  keys() {
    return this._map.keys();
  },
  entries() {
    return this._map.entries();
  },
  forEach(fn) {
    this._map.forEach(fn);
  },
  //@NOTE: some is not supported by Map, so we're faking it
  some(fn) {
    for (let [key, value] of this._map.entries()) {
      if (fn(value, key)) return true;
    }

    return false;
  }
});

const contentScripts = ['contentScript', 'contentScriptFile', 'contentScriptOptions', 'contentScriptWhen'];

/**
 * ExtendedPageMod constructor (exported below).
 * @constructor
 * @param {object} options - Configuration options found in site-configuration.js
 * @param {string} options.contentStyle -
 * @param {string[]} options.contentStyleFile - CSS files added to the page
 * @param {string} options.contentScript -
 * @param {string[]} options.contentScriptFile - Script files added to the page
 * @param {string} options.contentScriptOptions -  Data is added to a set of constants that are available on the content script
 * @param {string} options.contentScriptWhen - Document state to start worker, either 'start', 'ready', or end
 * @param {string[]} options.include - URL patterns to match against for including the script
 * @param {string[]} [options.exclude] - URL patterns to match against for excluding the script
 * @param {function} options.onAttach - Handles when the worker is attached
 * @param {function} options.onError - Possibly unused
 * @param {string[]} options.attachTo - Places to create the worker. 'top', 'frame', 'existing', or some combination are valid as long as 'top' or 'frame' is included
 */
const ExtendedPageMod = Class({
  extends: EventTarget,
  implements: [Disposable],
  attachTo: [],
  excludeURLs: null,
  include: null,
  setup(options) {
    this._onContent = this._onContent.bind(this);
    options = options || {};

    //@TODO: Determine whether validating all validationAttributes is the way to go,
    //or if this is even necessary
    let { contentStyle, contentStyleFile } = validate(options, validStyleOptions);

    contentScripts.forEach(script => {
      if (script in options) this[script] = options[script];
    });

    if ('onAttach' in options)
      this.on('attach', options.onAttach);
    //@TODO: Determine whether we are actually catching errors through the handler at all, when nowhere emits it
    if ('onError' in options)
      this.on('error', options.onError);
    if ('attachTo' in options) {
      if (typeof options.attachTo == 'string')
        this.attachTo = [options.attachTo];
      else if (Array.isArray(options.attachTo))
        this.attachTo = options.attachTo;
      else
        throw new Error('The `attachTo` option must be a string or an array ' +
          'of strings.');

      let isValidAttachToItem = function isValidAttachToItem(item) {
        return typeof item === 'string' &&
          VALID_ATTACHTO_OPTIONS.indexOf(item) !== -1;
      };

      if (!this.attachTo.every(isValidAttachToItem))
        throw new Error('The `attachTo` option valid accept only following ' +
          'values: '+ VALID_ATTACHTO_OPTIONS.join(', '));
      if (!hasAny(this.attachTo, ["top", "frame"]))
        throw new Error('The `attachTo` option must always contain at least' +
          ' `top` or `frame` value');
    }
    else {
      this.attachTo = ["top", "frame"];
    }

    //let exclude =  [].concat(options.exclude);
    let rules = this.include = new Rules();
    rules.on('add', this._onRuleAdd = this._onRuleAdd.bind(this));
    rules.on('remove', this._onRuleRemove = this._onRuleRemove.bind(this));
    rules.add(options.include);

    let exclude = this.exclude = new Rules();
    options.exclude && exclude.add(options.exclude);

    let styleRules = "";

    if (contentStyleFile)
      styleRules = [].concat(contentStyleFile).map(readURISync).join("");

    if (contentStyle)
      styleRules += [].concat(contentStyle).join("");

    if (styleRules) {
      this._onRuleUpdate = this._onRuleUpdate.bind(this);

      this._styleRules = styleRules;

      this._registerStyleSheet();
      rules.on('add', this._onRuleUpdate);
      rules.on('remove', this._onRuleUpdate);
    }

    this.on('error', this._onUncaughtError = this._onUncaughtError.bind(this));
    pageModManager.add(this);

    this._loadingWindows = [];

    // `_applyOnExistingDocuments` has to be called after `pageModManager.add()`
    // otherwise its calls to `_onContent` method won't do anything.
    if ('attachTo' in options && has(options.attachTo, 'existing')) {
      this._applyOnExistingDocuments();
    }
  },

  dispose() {
    this._unregisterStyleSheet();

    this.include.off('add', this._onRuleUpdate);
    this.include.off('remove', this._onRuleUpdate);

    //We need the Manager to remove all event handlers for this instance's urls
    this.include.remove([...this.include.keys()]); 

    pageModManager.remove(this);
    this._loadingWindows = [];
  },

  _loadingWindows: [],

  _isMatchingURI(uri) {
    return [...this.include.values()].some(pattern => pattern.test(uri));
  },

  _applyOnExistingDocuments() {
    getAllTabs()
      .filter(tab => this._isMatchingURI(getTabURI(tab)))
      .forEach(tab => {
      // Fake a newly created document
        let window = getTabContentWindow(tab);
        if (has(this.attachTo, "top"))
          this._onContent(window);
        if (has(this.attachTo, "frame"))
          getFrames(window).forEach(this._onContent);
      });
  },

  _onContent(window) {
    // If page is to be ignored
    var url = window.document.URL;
    for (let exclude of this.exclude.values()) {
      if(exclude.test(url)) return;
    }

    // not registered yet
    if (!pageModManager.has(this)) return;

    let isTopDocument = window.top === window;
    // Is a top level document and `top` is not set, ignore
    if (isTopDocument && !has(this.attachTo, "top"))
      return;
    // Is a frame document and `frame` is not set, ignore
    if (!isTopDocument && !has(this.attachTo, "frame"))
      return;

    // Immediatly evaluate content script if the document state is already
    // matching contentScriptWhen expectations
    let state = window.document.readyState;
    if ('start' === this.contentScriptWhen ||
      // Is `load` event already dispatched?
      'complete' === state ||
      // Is DOMContentLoaded already dispatched and waiting for it?
      ('ready' === this.contentScriptWhen && state === 'interactive') ) {
      this._createWorker(window);
      return;
    }

    let eventName = 'end' == this.contentScriptWhen ? 'load' : 'DOMContentLoaded';
    let self = this;
    window.addEventListener(eventName, function onReady(event) {
      if (event.target.defaultView != window)
        return;
      window.removeEventListener(eventName, onReady, true);

      self._createWorker(window);
    }, true);
  },
  _createWorker(window) {
    let worker = Worker({
      window: window,
      contentScript: this.contentScript,
      contentScriptFile: this.contentScriptFile,
      contentScriptOptions: this.contentScriptOptions,
      onError: this._onUncaughtError
    });
    emit(this, 'attach', worker);
    worker.once('detach', worker.destroy);
  },
  _onRuleAdd(url) {
    pageModManager.on(url, this._onContent);
  },
  _onRuleRemove(url) {
    pageModManager.off(url, this._onContent);
  },
  _onUncaughtError(e) {
    //@TODO: Determine if we actually only want console.exception when we lack an event handler
    if (count(this, 'error') == 1) console.exception(e);
  },
  _onRuleUpdate(){
    this._registerStyleSheet();
  },

  _registerStyleSheet() {
    let styleRules = this._styleRules;

    this._unregisterStyleSheet();

    let documentRules = [...this.include.values()].reduce(function (acc, pattern) {
      if (pattern.regexp)
        acc.push("regexp(\"" + pattern.regexp.source + "\")");
      else if (pattern.exactURL)
        acc.push("url(" + pattern.exactURL + ")");
      else if (pattern.domain)
        acc.push("domain(" + pattern.domain + ")");
      else if (pattern.urlPrefix)
        acc.push("url-prefix(" + pattern.urlPrefix + ")");
      else if (pattern.anyWebPage)
        acc.push("regexp(\"^(https?|ftp)://.*?\")");

      return acc;
    }, []);

    let uri = "data:text/css;charset=utf-8,";
    if (documentRules.length > 0) {
      uri += encodeURIComponent(`@-moz-document ${documentRules} {${styleRules}}`);
    }
    else {
      uri += encodeURIComponent(styleRules);
    }

    this._registeredStyleURI = io.newURI(uri, null, null);

    styleSheetService.loadAndRegisterSheet(
      this._registeredStyleURI,
      USER_SHEET
    );
  },

  _unregisterStyleSheet() {
    let uri = this._registeredStyleURI;

    if (uri && styleSheetService.sheetRegistered(uri, USER_SHEET)) {
      styleSheetService.unregisterSheet(uri, USER_SHEET);
    }

    this._registeredStyleURI = null;
  }
});
exports.ExtendedPageMod = options => ExtendedPageMod(options);
exports.ExtendedPageMod.prototype = ExtendedPageMod.prototype;

/**
 * ExtendedPageModManager manages all registed instances of ExtendedPageMod
 * It does most of this work on `document-element-inserted`
 * and then finding the instance associated with a window 
 */
const ExtendedPageModManager = Class({
  extends: EventTarget,
  implements: [Disposable],
  _off: EventTarget.prototype.off,
  _onError(e) {
    if (!count(this, 'error')) console.error(e);
  },
  has(instance) {
    let _registry = this._registry;
    return (
      (0 <= _registry.indexOf(instance)) /*||
        (instance && instance._public && 0 <= _registry.indexOf(instance._public))//*/
    );
  },
  add(instance) {
    let { _constructor, _registry } = this; 
    if (!(instance instanceof _constructor)) {
      instance = new _constructor(instance);
    }

    if (0 >_registry.indexOf(instance)) {
      _registry.push(instance);
      this.emit('add', instance);
    }
    return instance;
  },
  remove(instance) {
    let _registry = this._registry;
    let index = _registry.indexOf(instance);
    if (0 <= index) {
      this.emit('remove', instance);
      _registry.splice(index, 1);
    }
  },
  emit: selfEmit,
  setup() {
    this._registry = [];
    this._constructor = ExtendedPageMod;
    this.on('error', this._onError = this._onError.bind(this));

    events.on(
      'document-element-inserted',
      this._onContentWindow = this._onContentWindow.bind(this),
      true
    );
  },
  dispose() {
    events.off('document-element-inserted', this._onContentWindow);
    this._off();

    // We need to do some cleaning er ExtendedPageMods, like unregistering any
    // `contentStyle*`
    this._registry.forEach(pageMod => pageMod.destroy());

    //@TODO: Determine why we need a slice, when we aren't mutating anything?
    let _registry = this._registry.slice(0);
    //@TODO: Determine if there is any reason for this at all
    for (let instance of _registry) {
      this.emit('remove', instance);
    }

    //_registry.forEach(instance => this.emit('remove', instance));

    this._registry.splice(0); 
  },
  _onContentWindow(event) {
    let document = event.subject;
    let window = document.ownerGlobal;
    // XML documents don't have windows, and we don't yet support them.
    if (!window) {
      return;
    }
    // We apply only on documents in tabs of Firefox
    if (!getTabForContentWindow(window)) {
      return;
    }

    // When the tab is private, only addons with 'private-browsing' flag in
    // their package.json can apply content script to private documents
    if (ignoreWindow(window)) {
      return;
    }

    if (window.__contentScriptInjected) return;

    //@TODO:Determine if we need to iterate every instance & test or
    //is the first one enough
    this._registry.some(instance => {
      return instance.include.some((pattern, url) => {
        if (!pattern.test(document.URL)) return false;

        window.__contentScriptInjected = true;
        this.emit(url, window);

        return true;
      });
    });
  },
  off(topic, listener) {
    this._off(topic, listener);
    if (!count(this, topic)) {
      this._registry.forEach(instance => instance.include.remove(topic));
    }
  }
});
const pageModManager = new ExtendedPageModManager();

// Returns all tabs on all currently opened windows
function getAllTabs() {
  let tabs = [];
  // Iterate over all chrome windows
  for (let window in windowIterator()) {
    if (!isBrowser(window))
      continue;
    tabs = tabs.concat(getTabs(window));
  }
  return tabs;
}
