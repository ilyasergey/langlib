// site.js -- the two small things the pages need beyond static HTML: a
// light/dark override that survives navigation, and a table of contents that
// knows where you are. Everything else works with JavaScript switched off.

(function () {
  'use strict';

  var KEY = 'langlib-theme';

  function stored() {
    try { return localStorage.getItem(KEY); } catch (e) { return null; }
  }

  function apply(theme) {
    var root = document.documentElement;
    if (theme === 'light' || theme === 'dark') root.setAttribute('data-theme', theme);
    else root.removeAttribute('data-theme');
  }

  function current() {
    var t = document.documentElement.getAttribute('data-theme');
    if (t) return t;
    return window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches
      ? 'dark' : 'light';
  }

  apply(stored());

  document.addEventListener('DOMContentLoaded', function () {
    var button = document.querySelector('.theme-toggle');
    if (button) {
      var label = function () {
        button.textContent = current() === 'dark' ? 'light' : 'dark';
        button.setAttribute('aria-label', 'Switch to ' + button.textContent + ' theme');
      };
      label();
      button.addEventListener('click', function () {
        var next = current() === 'dark' ? 'light' : 'dark';
        apply(next);
        try { localStorage.setItem(KEY, next); } catch (e) { /* private window */ }
        label();
      });
      button.hidden = false;
    }

    // Highlight the table of contents entry for the section in view.
    var links = Array.prototype.slice.call(document.querySelectorAll('.toc a[href^="#"]'));
    if (links.length === 0 || !('IntersectionObserver' in window)) return;
    var byId = {};
    var targets = [];
    links.forEach(function (a) {
      var el = document.getElementById(decodeURIComponent(a.getAttribute('href').slice(1)));
      if (el) { byId[el.id] = a; targets.push(el); }
    });
    var seen = {};
    var observer = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) { seen[e.target.id] = e.isIntersecting; });
      var active = null;
      for (var i = 0; i < targets.length; i++) {
        if (seen[targets[i].id]) { active = targets[i].id; break; }
      }
      links.forEach(function (a) { a.style.color = ''; a.style.fontWeight = ''; });
      if (active && byId[active]) {
        byId[active].style.color = 'var(--accent)';
        byId[active].style.fontWeight = '600';
      }
    }, { rootMargin: '-70px 0px -70% 0px' });
    targets.forEach(function (t) { observer.observe(t); });
  });
})();
