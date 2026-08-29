// ws.js -- a Whitespace machine matching langlib's documented semantics.
//
// Follows docs/whitespace/spec.md, "Semantic decisions in langlib": integer
// values are arbitrary precision (BigInt here, Int in Lean), division and
// modulo round toward negative infinity with the sign of mod following the
// divisor, subtraction and friends compute `second op top`, labels are exact
// token strings with the first definition winning and undefined labels
// failing at jump time, copy errors and slide clamps, the heap is total and
// defaults to 0 with negative addresses an error, popping an empty stack is
// an error naming the instruction, running off the end is an error, number
// literals require a sign token, character I/O is byte oriented, readnum
// takes a whole line, and reading at end of input is an error.
//
// Fuel is one unit per executed instruction, labels included.
//
// Dependency-free; works in a browser (window.LangLibWS) and under node.

(function (root, factory) {
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  root.LangLibWS = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  var S = 'S', T = 'T', L = 'L';

  function ParseError(message) { this.name = 'ParseError'; this.message = message; }
  ParseError.prototype = Object.create(Error.prototype);

  // --- tokenising --------------------------------------------------------
  // Exactly space (0x20), tab (0x09) and LF (0x0A) are tokens. Everything
  // else, carriage return included, is a comment.
  function tokenize(src) {
    var toks = [], at = [];
    for (var i = 0; i < src.length; i++) {
      var c = src.charCodeAt(i);
      if (c === 0x20) { toks.push(S); at.push(i); }
      else if (c === 0x09) { toks.push(T); at.push(i); }
      else if (c === 0x0a) { toks.push(L); at.push(i); }
    }
    return { toks: toks, at: at };
  }

  // Human-readable rendering of the invisible source.
  var GLYPH = { S: '·', T: '→', L: '¶' };
  function glyphs(src) {
    var out = '';
    for (var i = 0; i < src.length; i++) {
      var c = src.charCodeAt(i);
      if (c === 0x20) out += GLYPH.S;
      else if (c === 0x09) out += GLYPH.T;
      else if (c === 0x0a) out += GLYPH.L + '\n';
      else out += src[i];
    }
    return out;
  }

  // --- parsing -----------------------------------------------------------

  function Parser(toks, at) { this.toks = toks; this.at = at; this.i = 0; }

  Parser.prototype.next = function (what) {
    if (this.i >= this.toks.length) {
      throw new ParseError('unexpected end of program while reading ' + what);
    }
    return this.toks[this.i++];
  };

  Parser.prototype.number = function () {
    var sign = this.next('a number');
    if (sign === L) throw new ParseError('number literal with no sign token');
    var neg = (sign === T);
    var value = 0n, tok;
    while ((tok = this.next('a number')) !== L) {
      value = value * 2n + (tok === T ? 1n : 0n);
    }
    return neg ? -value : value;
  };

  Parser.prototype.label = function () {
    var s = '', tok;
    while ((tok = this.next('a label')) !== L) s += tok;
    return s;
  };

  // A table of the instruction set, keyed by IMP then command tokens.
  // Each entry: [name, argumentKind]. argumentKind is 'num', 'label', or ''.
  var TABLE = {
    'S':   { 'S': ['push', 'num'], 'LS': ['dup', ''], 'LT': ['swap', ''],
             'LL': ['drop', ''], 'TS': ['copy', 'num'], 'TL': ['slide', 'num'] },
    'TS':  { 'SS': ['add', ''], 'ST': ['sub', ''], 'SL': ['mul', ''],
             'TS': ['div', ''], 'TT': ['mod', ''] },
    'TT':  { 'S': ['store', ''], 'T': ['retrieve', ''] },
    'L':   { 'SS': ['mark', 'label'], 'ST': ['call', 'label'], 'SL': ['jmp', 'label'],
             'TS': ['jz', 'label'], 'TT': ['jn', 'label'], 'TL': ['ret', ''],
             'LL': ['end', ''] },
    'TL':  { 'SS': ['outchar', ''], 'ST': ['outnum', ''],
             'TS': ['readchar', ''], 'TT': ['readnum', ''] }
  };

  function parse(src) {
    var t = tokenize(src);
    var p = new Parser(t.toks, t.at);
    var prog = [];
    while (p.i < p.toks.length) {
      var start = p.i;
      // The IMP is one token, except that a leading Tab takes a second.
      var imp = p.next('an instruction');
      if (imp === T) imp += p.next('an instruction');
      var table = TABLE[imp];
      if (!table) throw new ParseError('unknown instruction modification parameter');
      // Commands are one or two tokens; try one, then two.
      var cmd = p.next('a command');
      var entry = table[cmd];
      if (!entry) {
        cmd += p.next('a command');
        entry = table[cmd];
      }
      if (!entry) {
        throw new ParseError('unknown command ' + imp + '/' + cmd +
          ' at source offset ' + t.at[start]);
      }
      var ins = { op: entry[0], at: t.at[start], end: 0 };
      if (entry[1] === 'num') ins.arg = p.number();
      else if (entry[1] === 'label') ins.label = p.label();
      ins.end = p.i > 0 ? t.at[p.i - 1] : ins.at;
      prog.push(ins);
    }
    // Label table: the first definition of a label wins, because the
    // reference resolves labels by scanning from the start.
    var labels = Object.create(null);
    for (var k = 0; k < prog.length; k++) {
      if (prog[k].op === 'mark' && !(prog[k].label in labels)) {
        labels[prog[k].label] = k;
      }
    }
    return { prog: prog, labels: labels };
  }

  function disassemble(src) {
    var parsed = parse(src);
    return parsed.prog.map(function (ins, k) {
      var arg = ins.arg !== undefined ? ' ' + ins.arg
        : ins.label !== undefined ? ' ' + (ins.label === '' ? '<empty>' : ins.label)
        : '';
      return String(k).padStart(4, ' ') + '  ' + ins.op + arg;
    }).join('\n');
  }

  // --- floor division, as in Haskell's div/mod and Lean's fdiv/fmod ------
  function fdivmod(a, b) {
    var q = a / b, r = a % b;
    if (r !== 0n && ((r < 0n) !== (b < 0n))) { q -= 1n; r += b; }
    return [q, r];
  }

  function toBytes(x) {
    if (x == null) return new Uint8Array(0);
    if (x instanceof Uint8Array) return x;
    if (typeof TextEncoder !== 'undefined') return new TextEncoder().encode(String(x));
    var s = String(x), out = [];
    for (var i = 0; i < s.length; i++) out.push(s.charCodeAt(i) & 255);
    return new Uint8Array(out);
  }

  // As in bf.js: UTF-8 when the stream is UTF-8, one character per byte when
  // it is not, because outchar is byte-oriented and the byte is the point.
  function fromBytes(b) {
    if (typeof TextDecoder !== 'undefined') {
      try { return new TextDecoder('utf-8', { fatal: true }).decode(b); }
      catch (e) { /* not UTF-8; fall through */ }
    }
    return Array.prototype.map.call(b, function (c) { return String.fromCharCode(c); }).join('');
  }

  function Machine(source, input, options) {
    options = options || {};
    var parsed = parse(source);
    this.prog = parsed.prog;
    this.labels = parsed.labels;
    this.pc = 0;
    this.stack = [];
    this.heap = new Map();       // BigInt address (as string) -> BigInt
    this.calls = [];
    this.input = toBytes(input);
    this.inPos = 0;
    this.out = [];
    this.steps = 0;
    this.status = 'running';
    this.error = null;
  }

  Machine.prototype.fail = function (message) {
    this.status = 'error';
    this.error = message;
    return false;
  };

  Machine.prototype.pop = function (who) {
    if (this.stack.length === 0) { this.fail('empty stack in ' + who); return null; }
    return this.stack.pop();
  };

  Machine.prototype.heapGet = function (addr) { // the heap is total: 0 by default
    var v = this.heap.get(addr.toString());
    return v === undefined ? 0n : v;
  };

  Machine.prototype.step = function () {
    if (this.status !== 'running') return false;
    if (this.pc < 0 || this.pc >= this.prog.length) {
      this.steps++;
      return this.fail('ran off the end of the program without [LF][LF]');
    }
    var ins = this.prog[this.pc];
    var a, b, r, addr, target;
    this.steps++;
    switch (ins.op) {
      case 'push': this.stack.push(ins.arg); this.pc++; break;
      case 'dup':
        if (this.stack.length === 0) return this.fail('empty stack in dup');
        this.stack.push(this.stack[this.stack.length - 1]);
        this.pc++;
        break;
      case 'swap':
        if (this.stack.length < 2) return this.fail('stack too short in swap');
        a = this.stack.pop(); b = this.stack.pop();
        this.stack.push(a, b);
        this.pc++;
        break;
      case 'drop':
        if (this.pop('drop') === null) return false;
        this.pc++;
        break;
      case 'copy': {
        // Reference behaviour is Haskell's !!, so a negative or out of range
        // index is a runtime error.
        var n = ins.arg;
        if (n < 0n || n >= BigInt(this.stack.length)) {
          return this.fail('copy index ' + n + ' out of range');
        }
        this.stack.push(this.stack[this.stack.length - 1 - Number(n)]);
        this.pc++;
        break;
      }
      case 'slide': {
        // Haskell's drop: clamps at both ends, but still needs a top item.
        var top = this.pop('slide');
        if (top === null) return false;
        var k = ins.arg < 0n ? 0 : Number(ins.arg > BigInt(this.stack.length)
          ? BigInt(this.stack.length) : ins.arg);
        this.stack.length = this.stack.length - k;
        this.stack.push(top);
        this.pc++;
        break;
      }
      case 'add': case 'sub': case 'mul': case 'div': case 'mod': {
        if (this.stack.length < 2) return this.fail('stack too short in ' + ins.op);
        b = this.stack.pop();               // the top is the right operand
        a = this.stack.pop();
        if ((ins.op === 'div' || ins.op === 'mod') && b === 0n) {
          return this.fail(ins.op + ' by zero');
        }
        if (ins.op === 'add') r = a + b;
        else if (ins.op === 'sub') r = a - b;
        else if (ins.op === 'mul') r = a * b;
        else r = fdivmod(a, b)[ins.op === 'div' ? 0 : 1];
        this.stack.push(r);
        this.pc++;
        break;
      }
      case 'store': {
        var value = this.pop('store'); if (value === null) return false;
        addr = this.pop('store'); if (addr === null) return false;
        if (addr < 0n) return this.fail('negative heap address ' + addr);
        this.heap.set(addr.toString(), value);
        this.pc++;
        break;
      }
      case 'retrieve': {
        addr = this.pop('retrieve'); if (addr === null) return false;
        if (addr < 0n) return this.fail('negative heap address ' + addr);
        this.stack.push(this.heapGet(addr));
        this.pc++;
        break;
      }
      case 'mark': this.pc++; break;
      case 'call':
        target = this.labels[ins.label];
        if (target === undefined) return this.fail('undefined label in call');
        this.calls.push(this.pc + 1);
        this.pc = target;
        break;
      case 'jmp':
        target = this.labels[ins.label];
        if (target === undefined) return this.fail('undefined label in jump');
        this.pc = target;
        break;
      case 'jz': case 'jn': {
        var tested = this.pop(ins.op); if (tested === null) return false;
        var take = ins.op === 'jz' ? tested === 0n : tested < 0n;
        if (take) {
          target = this.labels[ins.label];
          if (target === undefined) return this.fail('undefined label in ' + ins.op);
          this.pc = target;
        } else this.pc++;
        break;
      }
      case 'ret':
        if (this.calls.length === 0) return this.fail('return with an empty call stack');
        this.pc = this.calls.pop();
        break;
      case 'end': this.status = 'halted'; return false;
      case 'outchar': {
        var ch = this.pop('outchar'); if (ch === null) return false;
        if (ch < 0n || ch > 255n) return this.fail('outchar value ' + ch + ' is not a byte');
        this.out.push(Number(ch));
        this.pc++;
        break;
      }
      case 'outnum': {
        var num = this.pop('outnum'); if (num === null) return false;
        var text = num.toString();
        for (var i = 0; i < text.length; i++) this.out.push(text.charCodeAt(i));
        this.pc++;
        break;
      }
      case 'readchar': {
        addr = this.pop('readchar'); if (addr === null) return false;
        if (addr < 0n) return this.fail('negative heap address ' + addr);
        if (this.inPos >= this.input.length) return this.fail('read at end of input');
        this.heap.set(addr.toString(), BigInt(this.input[this.inPos++]));
        this.pc++;
        break;
      }
      case 'readnum': {
        addr = this.pop('readnum'); if (addr === null) return false;
        if (addr < 0n) return this.fail('negative heap address ' + addr);
        if (this.inPos >= this.input.length) return this.fail('read at end of input');
        var line = '';
        while (this.inPos < this.input.length && this.input[this.inPos] !== 10) {
          line += String.fromCharCode(this.input[this.inPos++]);
        }
        if (this.inPos < this.input.length) this.inPos++;  // consume the newline
        if (!/^\s*-?[0-9]+\s*$/.test(line)) {
          return this.fail('readnum: ' + JSON.stringify(line) + ' is not a decimal integer');
        }
        this.heap.set(addr.toString(), BigInt(line.trim()));
        this.pc++;
        break;
      }
      default: return this.fail('unimplemented instruction ' + ins.op);
    }
    return this.status === 'running';
  };

  Machine.prototype.run = function (fuel) {
    if (fuel == null) fuel = 10000000;
    var spent = 0;
    while (this.status === 'running' && spent < fuel) { this.step(); spent++; }
    if (this.status === 'running') this.status = 'outoffuel';
    return this.status;
  };

  Machine.prototype.outputBytes = function () { return Uint8Array.from(this.out); };
  Machine.prototype.outputText = function () { return fromBytes(this.outputBytes()); };

  function run(source, input, options) {
    options = options || {};
    var m;
    try { m = new Machine(source, input, options); }
    catch (e) { return { status: 'parseerror', error: e.message, output: '', steps: 0 }; }
    m.run(options.fuel);
    return {
      status: m.status, error: m.error, output: m.outputText(),
      bytes: m.outputBytes(), steps: m.steps, machine: m
    };
  }

  return {
    Machine: Machine, ParseError: ParseError, parse: parse, tokenize: tokenize,
    glyphs: glyphs, GLYPH: GLYPH, disassemble: disassemble, run: run,
    fdivmod: fdivmod
  };
});
