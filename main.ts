// Tiny stack VM for make.fun's tiny-stack-vm-01 ISA (kit: generator/subject/ISA.md).
// One run answers every instance in /input/<id>/ (program.bin + input.bin) by
// writing /output/<id>/stdout.bin and /output/<id>/exit.txt. Node 22, builtins only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const SL = 1e6, OL = 65536;
// Per-opcode shape [opcode, immediate bytes, pops, pushes], from the ISA table.
// Bytes not listed are unknown opcodes, rejected before these numbers are used.
const K = new Uint8Array(256), I = new Uint8Array(256), A = new Uint8Array(256), B = new Uint8Array(256);
for (const [op, im, po, pu] of [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0],
]) { K[op] = 1; I[op] = im; A[op] = po; B[op] = pu; }
// Runs one program on one input; returns {o: bytes written, c: exit code}.
// A trap is thrown as its numeric code; a non-number throw is a bug here, exit 1.
function run(p, u) {
  const n = p.length, D = new Int32Array(256), C = new Int32Array(64),
    W = new Int32Array(256), O = new Uint8Array(OL);
  let s = 0, c = 0, pc = 0, t = 0, ip = 0, ol = 0;
  const ans = (e) => ({ o: O.subarray(0, ol), c: e });
  try {
    for (;;) {
      if (t === SL) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = p[pc];
      if (!K[op]) throw 5;
      const im = I[op];
      if (pc + im >= n) throw 9;
      t++;
      const nx = pc + 1 + im, po = A[op], pu = B[op];
      if (s < po) throw 2;
      if (s - po + pu > 256) throw 3;
      pc = nx;
      switch (op) {
        case 0: return ans(0); // HALT
        case 1: D[s++] = (p[pc - 1] << 24) >> 24; break; // PUSH8, sign-extended
        case 2: D[s++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24); break; // PUSH32 LE
        case 3: s--; break; // POP
        case 4: D[s] = D[s - 1]; s++; break; // DUP
        case 5: { const x = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = x; break; } // SWAP
        case 6: D[s] = D[s - 2]; s++; break; // OVER
        case 7: { const a = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = a; break; } // ROT
        case 23: D[s - 1] = (-D[s - 1]) | 0; break; // NEG, wraps
        case 27: D[s - 1] = ~D[s - 1]; break; // NOT
        case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24:
        case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
          const b = D[s - 1], a = D[s - 2];
          let r;
          if (op === 16) r = (a + b) | 0;
          else if (op === 17) r = (a - b) | 0;
          else if (op === 18) r = Math.imul(a, b);
          else if (op === 19) { if (!b) throw 4; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
          else if (op === 20) { if (!b) throw 4; r = b === -1 ? 0 : (a % b) | 0; }
          else if (op === 21) { if (!b) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
          else if (op === 22) { if (!b) throw 4; r = ((a >>> 0) % (b >>> 0)) | 0; }
          else if (op === 24) r = a & b;
          else if (op === 25) r = a | b;
          else if (op === 26) r = a ^ b;
          else if (op === 28) r = a << (b & 31);
          else if (op === 29) r = a >> (b & 31);
          else if (op === 30) r = (a >>> (b & 31)) | 0;
          else if (op === 32) r = a === b ? 1 : 0;
          else if (op === 33) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // 34 LTU
          D[s - 2] = r; s--;
          break;
        }
        case 48: case 49: case 50: { // JMP / JZ / JNZ, signed 16-bit offset from next
          const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
          let tk = 1;
          if (op !== 48) { const v = D[--s]; tk = op === 49 ? v === 0 : v !== 0; }
          if (tk) pc = nx + rel;
          break;
        }
        case 51: // CALL, unsigned 16-bit target, 64 return addresses max
          if (c === 64) throw 7;
          C[c++] = pc;
          pc = p[pc - 2] | (p[pc - 1] << 8);
          break;
        case 52: // RET
          if (!c) throw 8;
          pc = C[--c];
          break;
        case 64: { // LOAD
          const a = D[s - 1];
          if (a < 0 || a > 255) throw 6;
          D[s - 1] = W[a];
          break;
        }
        case 65: { // STORE: ( v addr -- )
          const a = D[s - 1], v = D[s - 2];
          if (a < 0 || a > 255) throw 6;
          s -= 2;
          W[a] = v;
          break;
        }
        case 80: { // PRINT: decimal ASCII, no newline; output limit checked first
          const g = String(D[s - 1]);
          if (ol + g.length > OL) throw 11;
          s--;
          for (let i = 0; i < g.length; i++) O[ol++] = g.charCodeAt(i);
          break;
        }
        case 81: // PUTC: one byte, v AND 255
          if (ol + 1 > OL) throw 11;
          O[ol++] = D[--s] & 255;
          break;
        case 82: // IN: next input byte, -1 once the input is used up
          D[s++] = ip < u.length ? u[ip++] : -1;
          break;
        case 83: return ans(D[--s] & 255); // EXIT: low byte is the code
        default: throw 5;
      }
    }
  } catch (e) {
    return ans(typeof e === 'number' ? e : 1);
  }
}
// Driver: one run over the whole set, in id order. A per-instance failure still
// writes that instance's answer files, so one bad instance cannot sink the other 39.
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN).sort()) {
  let r;
  try {
    r = run(readFileSync(join(IN, id, 'program.bin')), readFileSync(join(IN, id, 'input.bin')));
  } catch {
    r = { o: new Uint8Array(0), c: 0 };
  }
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), r.o);
  writeFileSync(join(OUT, id, 'exit.txt'), r.c + '\n');
}
