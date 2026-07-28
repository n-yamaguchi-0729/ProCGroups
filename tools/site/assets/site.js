
(function () {
  'use strict';

  const doc = document;
  const $ = (sel, root = doc) => root.querySelector(sel);
  const $$ = (sel, root = doc) => Array.from(root.querySelectorAll(sel));
  const rootPrefix = () => {
    const el = doc.querySelector('script[data-root]');
    return el ? el.getAttribute('data-root') || './' : './';
  };
  const linkHref = url => /^https?:\/\//i.test(url) ? url : rootPrefix() + url;
  const escapeHtml = s => String(s || '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

  function loadAsset(globalName, fileName) {
    if (window[globalName]) return Promise.resolve(window[globalName]);
    const key = '__loading_' + globalName;
    if (window[key]) return window[key];
    window[key] = new Promise((resolve, reject) => {
      const script = doc.createElement('script');
      script.src = rootPrefix() + fileName;
      script.defer = true;
      script.onload = () => resolve(window[globalName] || []);
      script.onerror = () => reject(new Error(fileName + ' could not be loaded'));
      doc.head.appendChild(script);
    });
    return window[key];
  }

  let searchData = null;
  function normalizeSearch(raw) {
    if (searchData) return searchData;
    searchData = (raw || []).map(item => {
      const name = item.n || '';
      const shortName = item.s || name.split('.').pop() || name;
      const moduleName = item.m || '';
      const kind = item.k || '';
      const statement = item.t || '';
      const url = item.u || '#';
      const haystack = [name, shortName, moduleName, kind, statement].join(' ').toLowerCase();
      return {name, shortName, moduleName, kind, statement, url, haystack,
        n: name.toLowerCase(), s: shortName.toLowerCase(), m: moduleName.toLowerCase()};
    });
    return searchData;
  }
  async function ensureSearchData() {
    return normalizeSearch(await loadAsset('LEAN_DOCS_INDEX', 'assets/search-index.js'));
  }
  function score(q, item) {
    if (item.n === q || item.s === q) return 140;
    if (item.s.startsWith(q)) return 115;
    if (item.n.endsWith('.' + q)) return 108;
    if (item.n.includes(q)) return 90;
    if (item.m.includes(q)) return 52;
    if (item.haystack.includes(q)) return 30;
    return 0;
  }
  async function search(query, limit) {
    const q = String(query || '').trim().toLowerCase();
    if (!q) return [];
    const data = await ensureSearchData();
    const scored = [];
    for (let i = 0; i < data.length; i++) {
      const s = score(q, data[i]);
      if (s) scored.push([s, data[i]]);
    }
    scored.sort((a, b) => b[0] - a[0] || a[1].name.localeCompare(b[1].name));
    return scored.slice(0, limit || 50).map(x => x[1]);
  }
  function resultHtml(item) {
    return '<span class="result-name">' + escapeHtml(item.name) + '</span>' +
      '<span class="result-meta">' + escapeHtml((item.kind || '') + (item.moduleName ? ' · ' + item.moduleName : '')) + '</span>';
  }

  function initAutocomplete() {
    const form = $('.search-form');
    const input = $('#search_input');
    const box = $('#autocomplete_results');
    if (!form || !input || !box) return;
    const params = new URLSearchParams(location.search);
    if (params.get('pattern')) input.value = params.get('pattern');
    let timer = 0;
    let seq = 0;
    async function render() {
      const current = ++seq;
      const q = input.value.trim();
      box.textContent = '';
      if (!q) return;
      const results = await search(q, 10).catch(() => []);
      if (current !== seq) return;
      const frag = doc.createDocumentFragment();
      for (const item of results) {
        const a = doc.createElement('a');
        a.href = linkHref(item.url);
        a.innerHTML = resultHtml(item);
        frag.appendChild(a);
      }
      box.appendChild(frag);
    }
    input.addEventListener('input', () => {
      clearTimeout(timer);
      timer = setTimeout(render, 90);
    });
    input.addEventListener('focus', () => { if (input.value.trim()) render(); });
    form.addEventListener('submit', ev => { if (!input.value.trim()) ev.preventDefault(); });
    doc.addEventListener('keydown', ev => {
      const tag = doc.activeElement ? doc.activeElement.tagName : '';
      if (ev.key === '/' && doc.activeElement !== input && !/input|textarea|select/i.test(tag)) {
        ev.preventDefault();
        input.focus();
      }
    });
    doc.addEventListener('click', ev => { if (!form.contains(ev.target)) box.textContent = ''; });
  }

  async function initFindPage() {
    const mount = $('#search_results');
    if (!mount) return;
    const q = (new URLSearchParams(location.search).get('pattern') || '').trim();
    mount.textContent = '';
    if (!q) {
      mount.innerHTML = '<div class="empty">Use the search box above to find libraries, modules, declarations, and statements.</div>';
      return;
    }
    const results = await search(q, 200).catch(() => []);
    const frag = doc.createDocumentFragment();
    const head = doc.createElement('div');
    head.className = 'meta';
    head.textContent = results.length + ' results';
    frag.appendChild(head);
    if (!results.length) {
      const empty = doc.createElement('div');
      empty.className = 'empty';
      empty.textContent = 'No matches.';
      frag.appendChild(empty);
    }
    for (const item of results) {
      const div = doc.createElement('div');
      div.className = 'search-result';
      div.innerHTML = '<a class="search-result-name" href="' + linkHref(item.url) + '">' + escapeHtml(item.name) + '</a>' +
        '<div class="result-meta">' + escapeHtml((item.kind || '') + (item.moduleName ? ' · ' + item.moduleName : '')) + '</div>' +
        (item.statement ? '<div class="search-result-doc">' + escapeHtml(item.statement) + '</div>' : '');
      frag.appendChild(div);
    }
    mount.appendChild(frag);
    if (window.MathJax && window.MathJax.startup && window.MathJax.startup.promise) {
      await window.MathJax.startup.promise;
    }
    if (window.MathJax && typeof window.MathJax.typesetPromise === 'function') {
      await window.MathJax.typesetPromise([mount]).catch(() => {});
    }
  }

  function initProofControls() {
    const details = $$('.proof-details');
    if (!details.length) return;
    doc.body.classList.add('has-proofs');
    const toggle = $('#toggle_all_proofs');
    const saved = localStorage.getItem('lean-docs-proof-open');
    const forceOpen = saved === 'all' || new URLSearchParams(location.search).get('proofs') === '1';
    const hash = location.hash.slice(1);
    const updateSummary = d => {
      const span = $('.summary-text', d);
      if (span) span.textContent = d.open ? 'Hide Lean proof' : 'Show Lean proof';
    };
    const allOpen = () => details.every(d => d.open);
    const updateButton = () => { if (toggle) toggle.textContent = allOpen() ? 'Hide all Lean proofs' : 'Show all Lean proofs'; };
    const mountProof = d => {
      const mount = $('.proof-mount', d);
      const template = $('.proof-template', d);
      if (mount && template && !mount.hasChildNodes()) mount.appendChild(template.content.cloneNode(true));
    };
    if (forceOpen) details.forEach(d => { d.open = true; });
    if (hash) {
      const target = doc.getElementById(hash);
      const d = target ? $('.proof-details', target) : null;
      if (d) d.open = true;
    }
    details.forEach(d => {
      if (d.open) mountProof(d);
      updateSummary(d);
      d.addEventListener('toggle', () => {
        if (d.open) mountProof(d);
        updateSummary(d);
        updateButton();
      });
    });
    if (toggle) {
      updateButton();
      toggle.addEventListener('click', () => {
        const next = !allOpen();
        details.forEach(d => {
          d.open = next;
          if (next) mountProof(d);
          updateSummary(d);
        });
        localStorage.setItem('lean-docs-proof-open', next ? 'all' : 'none');
        updateButton();
      });
    }
  }

  function initSortControls() {
    const numericKeys = new Set(['order', 'updated', 'decls', 'files', 'bundledModules', 'libraryModules', 'imports', 'importedBy', 'theorems', 'line']);
    const valueFor = (el, key) => {
      const value = el.dataset[key] || '';
      return numericKeys.has(key) ? Number(value || 0) : value.toLowerCase();
    };
    function compareItems(spec) {
      const parts = String(spec || 'order:asc').split(':');
      const key = parts[0] || 'order';
      const dir = parts[1] === 'desc' ? -1 : 1;
      return (a, b) => {
        const av = valueFor(a, key);
        const bv = valueFor(b, key);
        let result = 0;
        if (numericKeys.has(key)) {
          result = av === bv ? 0 : av < bv ? -1 : 1;
        } else {
          result = String(av).localeCompare(String(bv), 'en');
        }
        result *= dir;
        if (!result && key !== 'name') {
          result = String(valueFor(a, 'name')).localeCompare(String(valueFor(b, 'name')), 'en');
        }
        if (!result) {
          result = Number(a.dataset.order || 0) - Number(b.dataset.order || 0);
        }
        return result;
      };
    }
    function sortContainer(container, spec) {
      const items = Array.from(container.children).filter(el => el.hasAttribute('data-sort-item'));
      if (items.length < 2) return;
      items.sort(compareItems(spec));
      for (const item of items) container.appendChild(item);
    }
    const matchingSelect = (attr, value) => $$('select[' + attr + ']').find(el => el.getAttribute(attr) === value);
    const specForTarget = targetId => {
      const key = matchingSelect('data-sort-target', targetId);
      const dir = matchingSelect('data-sort-direction-target', targetId);
      return (key ? key.value : 'order') + ':' + (dir ? dir.value : 'asc');
    };
    const specForGroups = groups => {
      const key = matchingSelect('data-sort-groups', groups);
      const dir = matchingSelect('data-sort-direction-groups', groups);
      return (key ? key.value : 'order') + ':' + (dir ? dir.value : 'asc');
    };
    const applyTarget = targetId => {
      const target = doc.getElementById(targetId);
      if (target) sortContainer(target, specForTarget(targetId));
    };
    const applyGroups = groups => {
      for (const group of $$(groups)) sortContainer(group, specForGroups(groups));
    };
    for (const select of $$('select[data-sort-target], select[data-sort-direction-target]')) {
      const targetId = select.getAttribute('data-sort-target') || select.getAttribute('data-sort-direction-target');
      select.addEventListener('change', () => applyTarget(targetId));
    }
    for (const select of $$('select[data-sort-groups], select[data-sort-direction-groups]')) {
      const groups = select.getAttribute('data-sort-groups') || select.getAttribute('data-sort-direction-groups');
      select.addEventListener('change', () => applyGroups(groups));
    }
  }

  async function initTree() {
    const mount = $('#file_tree');
    if (!mount) return;
    const aside = $('.file-tree');
    const active = aside ? aside.getAttribute('data-active') || '' : '';
    const root = rootPrefix();
    const data = await loadAsset('LEAN_DOCS_TREE', 'assets/tree-data.js').catch(() => []);
    mount.textContent = '';
    if (!data.length) {
      mount.innerHTML = '<div class="tree-empty">No files.</div>';
      return;
    }
    function containsActive(node) {
      if (!active) return false;
      if (!node.c) return node.m === active;
      return node.c.some(containsActive);
    }
    function renderList(nodes) {
      const ul = doc.createElement('ul');
      ul.className = 'tree';
      for (const node of nodes) ul.appendChild(renderNode(node));
      return ul;
    }
    function renderNode(node) {
      const li = doc.createElement('li');
      if (node.c) {
        const activeBranch = containsActive(node);
        li.className = 'tree-dir' + (activeBranch ? ' contains-active' : '');
        const details = doc.createElement('details');
        const summary = doc.createElement('summary');
        summary.textContent = node.n;
        const children = doc.createElement('div');
        details.append(summary, children);
        if (activeBranch) {
          details.open = true;
          children.appendChild(renderList(node.c));
          details.dataset.loaded = '1';
        }
        details.addEventListener('toggle', () => {
          if (details.open && !details.dataset.loaded) {
            children.appendChild(renderList(node.c));
            details.dataset.loaded = '1';
          }
        }, {passive: true});
        li.appendChild(details);
      } else {
        li.className = 'tree-file' + (node.m === active ? ' active' : '');
        const a = doc.createElement('a');
        a.href = /^https?:\/\//i.test(node.u) ? node.u : root + node.u;
        a.textContent = node.n;
        if (node.m === active) a.setAttribute('aria-current', 'page');
        li.appendChild(a);
      }
      return li;
    }
    mount.appendChild(renderList(data));
    const current = $('.tree-file.active > a', mount);
    const pane = $('.tree-pane');
    if (current && pane) {
      const paneBox = pane.getBoundingClientRect();
      const itemBox = current.getBoundingClientRect();
      pane.scrollTop += itemBox.top - paneBox.top - (pane.clientHeight - itemBox.height) / 2;
    }
  }

  doc.addEventListener('DOMContentLoaded', () => {
    initAutocomplete();
    initFindPage();
    initProofControls();
    initSortControls();
    initTree();
  });
})();
