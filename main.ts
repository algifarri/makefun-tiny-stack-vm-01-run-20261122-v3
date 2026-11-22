// Tiny stack VM for make.fun's stack ISA v1. A trap keeps the output
// written so far, and its code becomes the program's exit code.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const SRC = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const DST = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const INT_MIN = -2147483648;

// Runs one program; traps are thrown as numbers and caught below.
function run(prog: Buffer, inp: Buffer): [Uint8Array, number] {
  const st = new Int32Array(256);
  const ra = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, rsp = 0, used = 0, pc = 0, steps = 0, read = 0;
  const len = prog.length;
  const done = (code: number): [Uint8Array, number] => [out.subarray(0, used), code];
  const need = (k: number) => { if (sp < k) throw 2; };  // stack underflow
  const room = () => { if (sp >= 256) throw 3; };       // stack overflow
  try {
    for (;;) {
      if (steps >= 1_000_000) throw 10;
      if (pc < 0 || pc >= len) throw 9;
      const op = prog[pc];
      const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
      const ok = op < 8 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34)
        || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
      if (!ok) throw 5;
      if (pc + imm >= len) throw 9;
      steps++;
      const next = pc + 1 + imm;
      pc = next;
      switch (op) {
        case 0x00: return done(0); // HALT
        case 0x01: room(); st[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
        case 0x02: room(); st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break; // PUSH32
        case 0x03: need(1); sp--; break; // POP
        case 0x04: need(1); room(); st[sp] = st[sp - 1]; sp++; break; // DUP
        case 0x05: { need(2); const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
        case 0x06: need(2); room(); st[sp] = st[sp - 2]; sp++; break; // OVER
        case 0x07: { need(3); const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; } // ROT ( a b c -- b c a )
        case 0x17: need(1); st[sp - 1] = -st[sp - 1] | 0; break; // NEG, wraps
        case 0x1b: need(1); st[sp - 1] = ~st[sp - 1]; break; // NOT
        case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed offset from next
          const off = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
          let go = true;
          if (op !== 0x30) { need(1); const v = st[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
          if (go) pc = next + off;
          break;
        }
        case 0x33: if (rsp >= 64) throw 7; ra[rsp++] = next; pc = prog[next - 2] | (prog[next - 1] << 8); break; // CALL, absolute target
        case 0x34: if (rsp < 1) throw 8; pc = ra[--rsp]; break; // RET
        case 0x40: { need(1); const a = st[sp - 1]; if (a < 0 || a > 255) throw 6; st[sp - 1] = mem[a]; break; } // LOAD
        case 0x41: { need(2); const a = st[sp - 1]; if (a < 0 || a > 255) throw 6; mem[a] = st[sp - 2]; sp -= 2; break; } // STORE ( v addr -- )
        case 0x50: { // PRINT, decimal ASCII
          need(1);
          const s = String(st[sp - 1]);
          if (used + s.length > 65536) throw 11;
          sp--;
          for (let i = 0; i < s.length; i++) out[used++] = s.charCodeAt(i);
          break;
        }
        case 0x51: need(1); if (used >= 65536) throw 11; out[used++] = st[--sp] & 255; break; // PUTC
        case 0x52: room(); st[sp++] = read < inp.length ? inp[read++] : -1; break; // IN, -1 past the end
        case 0x53: need(1); return done(st[--sp] & 255); // EXIT, low byte
        default: { // binary operators: 0x10..0x22 except NEG and NOT
          need(2);
          const b = st[sp - 1], a = st[sp - 2];
          let r: number;
          if (op === 0x10) r = (a + b) | 0; // ADD
          else if (op === 0x11) r = (a - b) | 0; // SUB
          else if (op === 0x12) r = Math.imul(a, b); // MUL, exact low 32 bits
          else if (op === 0x13) { if (!b) throw 4; r = a === INT_MIN && b === -1 ? INT_MIN : (a / b) | 0; } // DIV, truncates
          else if (op === 0x14) { if (!b) throw 4; r = b === -1 ? 0 : a % b; } // MOD, sign of a
          else if (op === 0x15) { if (!b) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
          else if (op === 0x16) { if (!b) throw 4; r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
          else if (op === 0x18) r = a & b; // AND
          else if (op === 0x19) r = a | b; // OR
          else if (op === 0x1a) r = a ^ b; // XOR
          else if (op === 0x1c) r = a << (b & 31); // SHL
          else if (op === 0x1d) r = a >> (b & 31); // SHR, arithmetic
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU, logical
          else if (op === 0x20) r = a === b ? 1 : 0; // EQ
          else if (op === 0x21) r = a < b ? 1 : 0; // LT, signed
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
          st[sp - 2] = r;
          sp--;
          break;
        }
      }
    }
  } catch (e) {
    if (typeof e === 'number') return done(e);
    throw e;
  }
}

for (const id of readdirSync(SRC).sort()) {
  const [bytes, code] = run(
    readFileSync(join(SRC, id, 'program.bin')),
    readFileSync(join(SRC, id, 'input.bin')),
  );
  mkdirSync(join(DST, id), { recursive: true });
  writeFileSync(join(DST, id, 'stdout.bin'), bytes);
  writeFileSync(join(DST, id, 'exit.txt'), `${code}\n`);
}
