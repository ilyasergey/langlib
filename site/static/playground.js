// playground.js -- wires the interpreters in bf.js, ws.js and df.js to the
// markup the generator emits. The interpreters know nothing about the DOM and
// the DOM code knows nothing about semantics, which is the only reason the
// node tests in site/test/ mean anything.
//
// A playground is a `.pg` element carrying data-kind ("brainfuck",
// "whitespace" or "deadfish") and data-examples (the id of a
// <script type="application/json"> element holding the example programs, all
// embedded at build time from Langlib/Examples/).

(function () {
  'use strict';

  // steps executed per animation tick, by slider position
  var SPEEDS = [1, 3, 12, 60, 400, 5000, Infinity];
  var SPEED_NAMES = ['1 step', '3', '12', '60', '400', '5000', 'all at once'];
  var TICK_MS = 16;
  var FUEL = 5000000;
  var MAX_SHOWN = 100000;

  var CONTROL_NAMES = {
    0: 'NUL', 7: 'BEL', 8: 'BS', 9: 'TAB', 10: 'LF', 13: 'CR', 27: 'ESC', 127: 'DEL'
  };

  function role(root, name) { return root.querySelector('[data-role="' + name + '"]'); }

  // A program that never halts can print megabytes before the step budget
  // runs out. The machine keeps all of it; the pane shows the start of it.
  function shown(text) {
    return text.length <= MAX_SHOWN ? text
      : text.slice(0, MAX_SHOWN) + '\n\u2026 output truncated at ' +
        MAX_SHOWN.toLocaleString() + ' characters';
  }

  function loadExamples(id) {
    var el = document.getElementById(id);
    if (!el) return [];
    try { return JSON.parse(el.textContent); } catch (e) { return []; }
  }

  function statusText(status) {
    switch (status) {
      case 'running': return 'running';
      case 'halted': return 'halted';
      case 'error': return 'runtime error';
      case 'outoffuel': return 'out of fuel';
      case 'parseerror': return 'parse error';
      default: return status;
    }
  }

  function setStatus(root, machineStatus, detail) {
    var el = role(root, 'status');
    if (!el) return;
    el.className = machineStatus;
    el.textContent = statusText(machineStatus) + (detail ? ': ' + detail : '');
  }

  function printable(byte) {
    if (byte in CONTROL_NAMES) return CONTROL_NAMES[byte];
    if (byte >= 32 && byte < 127) return String.fromCharCode(byte);
    return '·';
  }

  // A tiny driver shared by all three playgrounds: it owns the timer, the
  // Run/Pause button and the step budget, and calls back for rendering.
  function Driver(root, hooks) {
    this.root = root;
    this.hooks = hooks;
    this.timer = null;
    this.machine = null;
    var self = this;

    this.runButton = role(root, 'run');
    this.stepButton = role(root, 'step');
    this.resetButton = role(root, 'reset');
    this.speed = role(root, 'speed');
    this.speedLabel = role(root, 'speed-label');

    if (this.runButton) this.runButton.addEventListener('click', function () { self.toggle(); });
    if (this.stepButton) this.stepButton.addEventListener('click', function () { self.single(); });
    if (this.resetButton) this.resetButton.addEventListener('click', function () { self.reset(); });
    if (this.speed) {
      this.speed.addEventListener('input', function () { self.showSpeed(); });
      this.showSpeed();
    }

    ['program', 'input'].forEach(function (name) {
      var el = role(root, name);
      if (el) el.addEventListener('input', function () { self.reset(); });
    });
    ['eof', 'example'].forEach(function (name) {
      var el = role(root, name);
      if (el) el.addEventListener('change', function () { self.reset(); });
    });
  }

  Driver.prototype.showSpeed = function () {
    if (this.speedLabel) this.speedLabel.textContent = SPEED_NAMES[Number(this.speed.value)];
  };

  Driver.prototype.stepsPerTick = function () {
    return this.speed ? SPEEDS[Number(this.speed.value)] : Infinity;
  };

  Driver.prototype.ensure = function () {
    if (!this.machine) {
      this.machine = this.hooks.build();
      this.hooks.render(this.machine);
    }
    return this.machine;
  };

  Driver.prototype.reset = function () {
    this.stop();
    this.machine = null;
    this.hooks.clear();
  };

  Driver.prototype.single = function () {
    this.stop();
    var m = this.ensure();
    if (m && m.step) m.step();
    this.hooks.render(m);
  };

  Driver.prototype.stop = function () {
    if (this.timer !== null) { clearInterval(this.timer); this.timer = null; }
    if (this.runButton) this.runButton.textContent = 'Run';
  };

  Driver.prototype.toggle = function () {
    if (this.timer !== null) { this.stop(); return; }
    var m = this.ensure();
    if (!m || m.status !== 'running') {
      // Run on an already finished machine starts a fresh one.
      this.machine = null;
      this.hooks.clear();
      m = this.ensure();
      if (!m) return;
    }
    var perTick = this.stepsPerTick();
    if (perTick === Infinity) {
      m.run(FUEL);
      this.hooks.render(m);
      return;
    }
    var self = this;
    this.runButton.textContent = 'Pause';
    this.timer = setInterval(function () {
      var budget = perTick;
      while (budget-- > 0 && m.status === 'running') m.step();
      self.hooks.render(m);
      if (m.status !== 'running') self.stop();
    }, TICK_MS);
  };

  // ------------------------------------------------------------ brainfuck

  function mountBrainfuck(root) {
    var program = role(root, 'program');
    var input = role(root, 'input');
    var output = role(root, 'output');
    var tape = role(root, 'tape');
    var code = role(root, 'code');
    var steps = role(root, 'steps');
    var pointer = role(root, 'pointer');
    var eof = role(root, 'eof');
    var picker = role(root, 'example');
    var examples = loadExamples(root.getAttribute('data-examples'));
    var note = role(root, 'example-note');

    function renderTape(m) {
      if (!tape) return;
      var last = Math.max(m.highWater, m.ptr) + 1;
      var width = 32;
      var start = 0;
      if (last > width) start = Math.max(0, Math.min(m.ptr - (width >> 1), last - width));
      var end = Math.min(start + width, Math.max(last, start + 8));
      var html = '';
      for (var i = start; i < end; i++) {
        var v = m.tape[i] || 0;
        var cls = 'cell' + (v === 0 ? ' zero' : '') + (i === m.ptr ? ' here' : '');
        html += '<div class="' + cls + '"><span class="idx">' + i + '</span>' +
          '<span class="val">' + v + '</span>' +
          '<span class="chr">' + (v === 0 ? '' : escapeHtml(printable(v))) + '</span></div>';
      }
      tape.innerHTML = html;
    }

    function renderCode(m) {
      if (!code) return;
      var src = m.source;
      var at = m.status === 'running' ? m.sourceOffset() : -1;
      var out = '';
      for (var i = 0; i < src.length; i++) {
        var c = src[i];
        var esc = escapeHtml(c);
        var isOp = '+-<>.,[]'.indexOf(c) >= 0;
        if (i === at) out += '<mark>' + esc + '</mark>';
        else if (isOp) out += '<span class="op">' + esc + '</span>';
        else out += esc;
      }
      code.innerHTML = out;
      var mark = code.querySelector('mark');
      if (mark && mark.scrollIntoView) {
        var r = mark.offsetTop - code.scrollTop;
        if (r < 0 || r > code.clientHeight - 20) code.scrollTop = mark.offsetTop - code.clientHeight / 2;
      }
    }

    function render(m) {
      if (!m) return;
      if (output) output.textContent = shown(m.outputText());
      renderTape(m);
      renderCode(m);
      if (steps) steps.textContent = m.steps.toLocaleString() + ' steps';
      if (pointer) pointer.textContent = 'pointer at cell ' + m.ptr +
        ' · ' + (m.input.length - m.inPos) + ' input bytes left';
      setStatus(root, m.status, m.error);
    }

    function clear() {
      if (output) output.textContent = '';
      if (code) code.textContent = '';
      if (tape) tape.innerHTML = '';
      if (steps) steps.textContent = '';
      if (pointer) pointer.textContent = '';
      setStatus(root, 'running', 'not started');
    }

    function build() {
      try {
        return new window.LangLibBF.Machine(program.value, input ? input.value : '',
          { eof: eof ? eof.value : 'unchanged' });
      } catch (e) {
        setStatus(root, 'parseerror', e.message);
        if (output) output.textContent = '';
        return null;
      }
    }

    var driver = new Driver(root, { build: build, render: render, clear: clear });

    if (picker && examples.length) {
      examples.forEach(function (ex, i) {
        var o = document.createElement('option');
        o.value = String(i);
        o.textContent = ex.name;
        picker.appendChild(o);
      });
      picker.addEventListener('change', function () {
        var ex = examples[Number(picker.value)];
        if (!ex) return;
        program.value = ex.source;
        if (input) input.value = ex.input || '';
        if (eof) eof.value = ex.eof || 'unchanged';
        if (note) note.textContent = ex.note || '';
        driver.reset();
      });
      picker.value = '0';
      picker.dispatchEvent(new Event('change'));
    }
    clear();
  }

  // ----------------------------------------------------------- whitespace

  function mountWhitespace(root) {
    var program = role(root, 'program');
    var input = role(root, 'input');
    var output = role(root, 'output');
    var glyphs = role(root, 'glyphs');
    var listing = role(root, 'listing');
    var stack = role(root, 'stack');
    var heap = role(root, 'heap');
    var steps = role(root, 'steps');
    var picker = role(root, 'example');
    var examples = loadExamples(root.getAttribute('data-examples'));
    var note = role(root, 'example-note');

    function renderGlyphs() {
      if (!glyphs) return;
      var src = program.value;
      var out = '';
      for (var i = 0; i < src.length; i++) {
        var c = src.charCodeAt(i);
        if (c === 0x20) out += '<span class="g-s">·</span>';
        else if (c === 0x09) out += '<span class="g-t">→</span>';
        else if (c === 0x0a) out += '<span class="g-l">¶</span>\n';
        else out += escapeHtml(src[i]);
      }
      glyphs.innerHTML = out;
    }

    function renderListing(m) {
      if (!listing) return;
      var html = '';
      for (var i = 0; i < m.prog.length; i++) {
        var ins = m.prog[i];
        var arg = ins.arg !== undefined ? ' ' + ins.arg
          : ins.label !== undefined ? ' ' + (ins.label === '' ? '∅' : ins.label)
          : '';
        var line = String(i).padStart(3, ' ') + '  ' + ins.op + arg;
        html += (i === m.pc && m.status === 'running')
          ? '<mark>' + escapeHtml(line) + '</mark>\n'
          : escapeHtml(line) + '\n';
      }
      listing.innerHTML = html;
      var mark = listing.querySelector('mark');
      if (mark) {
        var r = mark.offsetTop - listing.scrollTop;
        if (r < 0 || r > listing.clientHeight - 20) {
          listing.scrollTop = mark.offsetTop - listing.clientHeight / 2;
        }
      }
    }

    function render(m) {
      if (!m) return;
      if (output) output.textContent = shown(m.outputText());
      renderListing(m);
      if (stack) {
        stack.textContent = m.stack.length === 0 ? ''
          : m.stack.slice().reverse().map(function (v, i) {
              return (i === 0 ? 'top ' : '    ') + v.toString();
            }).join('\n');
      }
      if (heap) {
        var keys = Array.from(m.heap.keys()).sort(function (a, b) { return Number(a) - Number(b); });
        heap.textContent = keys.map(function (k) {
          return '[' + k + '] = ' + m.heap.get(k).toString();
        }).join('\n');
      }
      if (steps) steps.textContent = m.steps.toLocaleString() + ' steps';
      setStatus(root, m.status, m.error);
    }

    function clear() {
      if (output) output.textContent = '';
      if (stack) stack.textContent = '';
      if (heap) heap.textContent = '';
      if (listing) listing.textContent = '';
      if (steps) steps.textContent = '';
      renderGlyphs();
      setStatus(root, 'running', 'not started');
      try {
        var d = window.LangLibWS.parse(program.value);
        if (listing) {
          listing.textContent = d.prog.map(function (ins, i) {
            var arg = ins.arg !== undefined ? ' ' + ins.arg
              : ins.label !== undefined ? ' ' + (ins.label === '' ? '∅' : ins.label) : '';
            return String(i).padStart(3, ' ') + '  ' + ins.op + arg;
          }).join('\n');
        }
      } catch (e) {
        setStatus(root, 'parseerror', e.message);
      }
    }

    function build() {
      try {
        return new window.LangLibWS.Machine(program.value, input ? input.value : '', {});
      } catch (e) {
        setStatus(root, 'parseerror', e.message);
        return null;
      }
    }

    var driver = new Driver(root, { build: build, render: render, clear: clear });
    if (program) program.addEventListener('input', renderGlyphs);

    if (picker && examples.length) {
      examples.forEach(function (ex, i) {
        var o = document.createElement('option');
        o.value = String(i);
        o.textContent = ex.name;
        picker.appendChild(o);
      });
      picker.addEventListener('change', function () {
        var ex = examples[Number(picker.value)];
        if (!ex) return;
        program.value = ex.source;
        if (input) input.value = ex.input || '';
        if (note) note.textContent = ex.note || '';
        driver.reset();
      });
      picker.value = '0';
      picker.dispatchEvent(new Event('change'));
    }
    clear();
  }

  // ------------------------------------------------------------- deadfish

  function mountDeadfish(root) {
    var program = role(root, 'program');
    var output = role(root, 'output');
    var acc = role(root, 'acc');
    var code = role(root, 'code');
    var steps = role(root, 'steps');
    var picker = role(root, 'example');
    var examples = loadExamples(root.getAttribute('data-examples'));

    function render(m) {
      if (!m) return;
      if (output) output.textContent = shown(m.out);
      if (acc) {
        acc.textContent = m.acc.toString();
        acc.className = 'pg-out df-acc' + (m.reset ? ' reset' : '');
      }
      if (code) {
        var src = m.source, html = '';
        for (var i = 0; i < src.length; i++) {
          var c = escapeHtml(src[i]);
          html += (i === m.pc && m.status === 'running') ? '<mark>' + c + '</mark>'
            : ('idso'.indexOf(src[i]) >= 0 ? '<span class="op">' + c + '</span>' : c);
        }
        code.innerHTML = html;
      }
      if (steps) steps.textContent = m.steps.toLocaleString() + ' steps';
      setStatus(root, m.status, null);
    }

    function clear() {
      if (output) output.textContent = '';
      if (acc) { acc.textContent = '0'; acc.className = 'pg-out df-acc'; }
      if (code) code.textContent = '';
      if (steps) steps.textContent = '';
      setStatus(root, 'running', 'not started');
    }

    function build() { return new window.LangLibDF.Machine(program.value); }

    var driver = new Driver(root, { build: build, render: render, clear: clear });

    if (picker && examples.length) {
      examples.forEach(function (ex, i) {
        var o = document.createElement('option');
        o.value = String(i);
        o.textContent = ex.name;
        picker.appendChild(o);
      });
      picker.addEventListener('change', function () {
        var ex = examples[Number(picker.value)];
        if (!ex) return;
        program.value = ex.source;
        driver.reset();
      });
      picker.value = '0';
      picker.dispatchEvent(new Event('change'));
    }
    clear();
  }

  function escapeHtml(s) {
    return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  document.addEventListener('DOMContentLoaded', function () {
    Array.prototype.forEach.call(document.querySelectorAll('.pg[data-kind]'), function (root) {
      switch (root.getAttribute('data-kind')) {
        case 'brainfuck': mountBrainfuck(root); break;
        case 'whitespace': mountWhitespace(root); break;
        case 'deadfish': mountDeadfish(root); break;
      }
    });
  });
})();
