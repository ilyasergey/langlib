// bf.js -- a brainfuck machine matching langlib's documented semantics.
//
// The semantics implemented here are exactly the ones pinned down in
// docs/brainfuck/spec.md, "Semantic decisions in langlib":
//
//   1. cells are 8 bits and wrap;
//   2. the tape is unbounded to the right (grown on demand, all zero);
//   3. moving left of cell 0 is a runtime error;
//   4. `,` at end of input leaves the cell unchanged by default, with the
//      `zero` and `minus1` (store 255) conventions selectable;
//   5. no newline translation, bytes go in and out untouched.
//
// Fuel is charged one unit per primitive command and per loop-condition
// check, as in Langlib/Languages/Brainfuck/Semantics.lean.
//
// The file is dependency-free and runs both in a browser (defines
// window.LangLibBF) and under node (module.exports), so the same code is
// tested by site/test/bf-test.mjs.

(function (root, factory) {
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  root.LangLibBF = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  var OPS = '+-<>.,[]';

  function ParseError(message, offset) {
    this.name = 'ParseError';
    this.message = message;
    this.offset = offset;
  }
  ParseError.prototype = Object.create(Error.prototype);

  // Strip comment characters and match brackets. Returns the compiled
  // program: the op string, the source offset of each op (for highlighting),
  // and a jump table pairing every `[` with its `]`.
  function compile(src) {
    var ops = [];
    var at = [];
    for (var i = 0; i < src.length; i++) {
      if (OPS.indexOf(src[i]) >= 0) { ops.push(src[i]); at.push(i); }
    }
    var jump = new Int32Array(ops.length);
    var stack = [];
    for (var k = 0; k < ops.length; k++) {
      if (ops[k] === '[') stack.push(k);
      else if (ops[k] === ']') {
        if (stack.length === 0) {
          throw new ParseError('unmatched ] at source offset ' + at[k], at[k]);
        }
        var open = stack.pop();
        jump[k] = open;
        jump[open] = k;
      }
    }
    if (stack.length > 0) {
      var last = stack[stack.length - 1];
      throw new ParseError('unmatched [ at source offset ' + at[last], at[last]);
    }
    return { ops: ops.join(''), at: at, jump: jump };
  }

  function toBytes(x) {
    if (x == null) return new Uint8Array(0);
    if (x instanceof Uint8Array) return x;
    if (typeof TextEncoder !== 'undefined') return new TextEncoder().encode(String(x));
    var s = String(x), out = [];
    for (var i = 0; i < s.length; i++) out.push(s.charCodeAt(i) & 255);
    return new Uint8Array(out);
  }

  function fromBytes(bytes) {
    if (typeof TextDecoder !== 'undefined') {
      return new TextDecoder('utf-8').decode(bytes);
    }
    var s = '';
    for (var i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
    return s;
  }

  // eof: 'unchanged' (default, Mueller's interpreter), 'zero', or 'minus1'
  // (store 255). These are the three the runner offers as --eof.
  function Machine(source, input, options) {
    options = options || {};
    var program = compile(source);
    this.ops = program.ops;
    this.at = program.at;
    this.jump = program.jump;
    this.source = source;
    this.eof = options.eof || 'unchanged';
    this.tape = new Uint8Array(options.initialTape || 1024);
    this.ptr = 0;
    this.pc = 0;
    this.highWater = 0;          // rightmost cell ever visited
    this.input = toBytes(input);
    this.inPos = 0;
    this.out = [];
    this.steps = 0;
    this.status = 'running';     // running | halted | error | outoffuel
    this.error = null;
  }

  Machine.prototype.grow = function () {
    var bigger = new Uint8Array(this.tape.length * 2);
    bigger.set(this.tape);
    this.tape = bigger;
  };

  Machine.prototype.fail = function (message) {
    this.status = 'error';
    this.error = message;
  };

  // One primitive command or loop-condition check. Returns true if the
  // machine is still running afterwards.
  Machine.prototype.step = function () {
    if (this.status !== 'running') return false;
    if (this.pc >= this.ops.length) { this.status = 'halted'; return false; }
    var t = this.tape, p = this.ptr;
    switch (this.ops[this.pc]) {
      case '+': t[p] = (t[p] + 1) & 255; this.pc++; break;
      case '-': t[p] = (t[p] + 255) & 255; this.pc++; break;
      case '>':
        this.ptr++;
        if (this.ptr >= this.tape.length) this.grow();
        if (this.ptr > this.highWater) this.highWater = this.ptr;
        this.pc++;
        break;
      case '<':
        if (this.ptr === 0) {
          this.steps++;
          this.fail('moved left of cell 0 (source offset ' + this.at[this.pc] + ')');
          return false;
        }
        this.ptr--;
        this.pc++;
        break;
      case '.': this.out.push(t[p]); this.pc++; break;
      case ',':
        if (this.inPos < this.input.length) t[p] = this.input[this.inPos++];
        else if (this.eof === 'zero') t[p] = 0;
        else if (this.eof === 'minus1') t[p] = 255;
        // 'unchanged': the cell keeps whatever it held.
        this.pc++;
        break;
      case '[': this.pc = (t[p] === 0) ? this.jump[this.pc] + 1 : this.pc + 1; break;
      case ']': this.pc = (t[p] !== 0) ? this.jump[this.pc] + 1 : this.pc + 1; break;
    }
    this.steps++;
    if (this.pc >= this.ops.length) this.status = 'halted';
    return this.status === 'running';
  };

  // Run at most `fuel` steps. Sets status to 'outoffuel' if the budget runs
  // out while the machine is still running, matching the runner's exit code 2.
  Machine.prototype.run = function (fuel) {
    if (fuel == null) fuel = 200000000;
    var spent = 0;
    while (this.status === 'running' && spent < fuel) {
      this.step();
      spent++;
    }
    if (this.status === 'running') this.status = 'outoffuel';
    return this.status;
  };

  Machine.prototype.outputBytes = function () { return Uint8Array.from(this.out); };
  Machine.prototype.outputText = function () { return fromBytes(this.outputBytes()); };
  Machine.prototype.sourceOffset = function () {
    return this.pc < this.at.length ? this.at[this.pc] : this.source.length;
  };

  // Convenience wrapper: run a program to completion and report everything.
  function run(source, input, options) {
    options = options || {};
    var m;
    try {
      m = new Machine(source, input, options);
    } catch (e) {
      return { status: 'parseerror', error: e.message, output: '', steps: 0 };
    }
    m.run(options.fuel);
    return {
      status: m.status,
      error: m.error,
      output: m.outputText(),
      bytes: m.outputBytes(),
      steps: m.steps,
      machine: m
    };
  }

  return {
    Machine: Machine,
    ParseError: ParseError,
    compile: compile,
    run: run,
    toBytes: toBytes,
    fromBytes: fromBytes
  };
});
