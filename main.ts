// Tiny stack VM, ISA v1..
import { mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const STEPS = 1000000, SCAP = 256, CCAP = 64, MEM = 256, OCAP = 65536;

class Trap extends Error {
  code: number;
  constructor(code: number) { super('trap ' + code); this.code = code; }
}

function shape(op: number): [number, number, number] | null {
  if (op === 0) return [0, 0, 0];
  if (op === 1) return [1, 0, 1];
  if (op === 2) return [4, 0, 1];
  if (op === 3) return [0, 1, 0];
  if (op === 4) return [0, 1, 2];
  if (op === 5) return [0, 2, 2];
  if (op === 6) return [0, 2, 3];
  if (op === 7) return [0, 3, 3];
  if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) return [0, 2, 1];
  if (op === 0x17 || op === 0x1b) return [0, 1, 1];
  if (op === 0x30) return [2, 0, 0];
  if (op === 0x31 || op === 0x32) return [2, 1, 0];
  if (op === 0x33) return [2, 0, 0];
  if (op === 0x34) return [0, 0, 0];
  if (op === 0x40) return [0, 1, 1];
  if (op === 0x41) return [0, 2, 0];
  if (op === 0x50 || op === 0x51) return [0, 1, 0];
  if (op === 0x52) return [0, 0, 1];
  if (op === 0x53) return [0, 1, 0];
  return null;
}

const u16 = (b: Uint8Array, i: number) => b[i] | (b[i + 1] << 8);
const i16 = (b: Uint8Array, i: number) => (u16(b, i) << 16) >> 16;
const i32 = (b: Uint8Array, i: number) => b[i] | (b[i + 1] << 8) | (b[i + 2] << 16) | (b[i + 3] << 24);

function combine(op: number, a: number, b: number): number {
  switch (op) {
    case 0x10: return (a + b) | 0;
    case 0x11: return (a - b) | 0;
    case 0x12: return Math.imul(a, b);
    case 0x13:
      if (b === 0) throw new Trap(4);
      return a === -2147483648 && b === -1 ? a : (a / b) | 0;
    case 0x14:
      if (b === 0) throw new Trap(4);
      return b === -1 ? 0 : (a % b) | 0;
    case 0x15:
      if (b === 0) throw new Trap(4);
      return ((a >>> 0) / (b >>> 0)) | 0;
    case 0x16:
      if (b === 0) throw new Trap(4);
      return ((a >>> 0) % (b >>> 0)) | 0;
    case 0x18: return a & b;
    case 0x19: return a | b;
    case 0x1a: return a ^ b;
    case 0x1c: return a << (b & 31);
    case 0x1d: return a >> (b & 31);
    case 0x1e: return (a >>> (b & 31)) | 0;
    case 0x20: return a === b ? 1 : 0;
    case 0x21: return a < b ? 1 : 0;
    default: return (a >>> 0) < (b >>> 0) ? 1 : 0;
  }
}

class Machine {
  private prog: Uint8Array; private feed: Uint8Array;
  private pc = 0; private done = 0;
  private vals = new Int32Array(SCAP); private n = 0;
  private rets = new Int32Array(CCAP); private rn = 0;
  private cells = new Int32Array(MEM);
  private sink = new Uint8Array(OCAP); private w = 0; private r = 0;

  constructor(prog: Uint8Array, feed: Uint8Array) { this.prog = prog; this.feed = feed; }
  private peek(k: number) { return this.vals[this.n - 1 - k]; }
  private pop() { return this.vals[--this.n]; }
  private push(v: number) { this.vals[this.n++] = v | 0; }
  private emit(s: string) {
    if (this.w + s.length > OCAP) throw new Trap(11);
    this.sink.set(new TextEncoder().encode(s), this.w); this.w += s.length;
  }
  private emitByte(v: number) {
    if (this.w + 1 > OCAP) throw new Trap(11);
    this.sink[this.w++] = v & 255;
  }
  private step(): number | null {
    if (this.done === STEPS) throw new Trap(10);
    if (this.pc < 0 || this.pc >= this.prog.length) throw new Trap(9);
    const op = this.prog[this.pc];
    const spec = shape(op);
    if (spec === null) throw new Trap(5);
    const [imm, pops, pushes] = spec;
    if (this.pc + imm >= this.prog.length) throw new Trap(9);
    this.done++;
    if (this.n < pops) throw new Trap(2);
    if (this.n - pops + pushes > SCAP) throw new Trap(3);
    const after = this.pc + 1 + imm;
    this.pc = after;
    switch (op) {
      case 0x00: return 0;
      case 0x01: this.push((this.prog[after - 1] << 24) >> 24); break;
      case 0x02: this.push(i32(this.prog, after - 4)); break;
      case 0x03: this.n--; break;
      case 0x04: this.push(this.peek(0)); break;
      case 0x05: {
        const t = this.peek(0);
        this.vals[this.n - 1] = this.peek(1); this.vals[this.n - 2] = t;
        break;
      }
      case 0x06: this.push(this.peek(1)); break;
      case 0x07: {
        const t = this.peek(2);
        this.vals[this.n - 3] = this.peek(1); this.vals[this.n - 2] = this.peek(0);
        this.vals[this.n - 1] = t;
        break;
      }
      case 0x17: this.vals[this.n - 1] = -this.peek(0) | 0; break;
      case 0x1b: this.vals[this.n - 1] = ~this.peek(0); break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = this.pop(), a = this.pop();
        this.push(combine(op, a, b));
        break;
      }
      case 0x30: this.pc = after + i16(this.prog, after - 2); break;
      case 0x31: case 0x32: {
        const v = this.pop();
        if ((op === 0x31) === (v === 0)) this.pc = after + i16(this.prog, after - 2);
        break;
      }
      case 0x33:
        if (this.rn === CCAP) throw new Trap(7);
        this.rets[this.rn++] = after; this.pc = u16(this.prog, after - 2);
        break;
      case 0x34:
        if (this.rn === 0) throw new Trap(8);
        this.pc = this.rets[--this.rn];
        break;
      case 0x40: {
        const addr = this.peek(0);
        if (addr < 0 || addr >= MEM) throw new Trap(6);
        this.vals[this.n - 1] = this.cells[addr];
        break;
      }
      case 0x41: {
        const addr = this.pop(), v = this.pop();
        if (addr < 0 || addr >= MEM) throw new Trap(6);
        this.cells[addr] = v;
        break;
      }
      case 0x50: this.emit(String(this.pop())); break;
      case 0x51: this.emitByte(this.pop()); break;
      case 0x52: this.push(this.r < this.feed.length ? this.feed[this.r++] : -1); break;
      case 0x53: return this.pop() & 255;
    }
    return null;
  }
  run(): { bytes: Uint8Array; code: number } {
    try {
      for (;;) {
        const code = this.step();
        if (code !== null) return { bytes: this.sink.subarray(0, this.w), code };
      }
    } catch (err) {
      if (err instanceof Trap) return { bytes: this.sink.subarray(0, this.w), code: err.code };
      throw err;
    }
  }
}

function readOpt(p: string): Uint8Array {
  try { return readFileSync(p); } catch { return new Uint8Array(0); }
}

for (const name of readdirSync(IN).sort()) {
  const dir = join(IN, name);
  if (!statSync(dir).isDirectory()) continue;
  const { bytes, code } = new Machine(
    readOpt(join(dir, 'program.bin')), readOpt(join(dir, 'input.bin'))).run();
  const outDir = join(OUT, name);
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, 'stdout.bin'), bytes);
  writeFileSync(join(outDir, 'exit.txt'), code + '\n');
}
