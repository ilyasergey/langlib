// df.js -- a Deadfish machine matching langlib's documented semantics.
//
// Follows docs/deadfish/spec.md: one unbounded accumulator; `i`, `d`, `s`,
// `o`; every other character prints a bare newline; the accumulator resets
// to 0 exactly when it is -1 or 256, checked after each of i, d, s. No
// input, no control flow, no halt command, no prompt. One fuel unit per
// command, so an n-character program halts in exactly n steps.
//
// Values are BigInt because squaring gets out of hand quickly.
//
// Dependency-free; works in a browser (window.LangLibDF) and under node.

(function (root, factory) {
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  root.LangLibDF = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  function Machine(source) {
    this.source = source;
    this.pc = 0;
    this.acc = 0n;
    this.out = '';
    this.steps = 0;
    this.status = source.length === 0 ? 'halted' : 'running';
    this.lastOp = null;
    this.reset = false;   // did the previous step trip the reset?
  }

  function normalize(m) {
    // The one interesting rule, and it is an exact comparison, not a clamp.
    if (m.acc === -1n || m.acc === 256n) { m.acc = 0n; m.reset = true; }
    else m.reset = false;
  }

  Machine.prototype.step = function () {
    if (this.status !== 'running') return false;
    var c = this.source[this.pc];
    this.lastOp = c;
    this.reset = false;
    switch (c) {
      case 'i': this.acc += 1n; normalize(this); break;
      case 'd': this.acc -= 1n; normalize(this); break;
      case 's': this.acc *= this.acc; normalize(this); break;
      case 'o': this.out += this.acc.toString() + '\n'; break;
      default:  this.out += '\n'; break;   // errors are not acknowledged
    }
    this.pc++;
    this.steps++;
    if (this.pc >= this.source.length) this.status = 'halted';
    return this.status === 'running';
  };

  Machine.prototype.run = function (fuel) {
    if (fuel == null) fuel = 1000000;
    var spent = 0;
    while (this.status === 'running' && spent < fuel) { this.step(); spent++; }
    if (this.status === 'running') this.status = 'outoffuel';
    return this.status;
  };

  function run(source, options) {
    options = options || {};
    var m = new Machine(source);
    m.run(options.fuel);
    return { status: m.status, output: m.out, steps: m.steps, machine: m };
  }

  return { Machine: Machine, run: run };
});
