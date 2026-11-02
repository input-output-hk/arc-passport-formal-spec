// Explicit process-owned primitive backend for Haskell/C clients. One bare oracle
// request per input line, one reply per output line; errors terminate nonzero.
// No fake cryptography, monitor subprocess, or process-global callback bridge.
import { createInterface } from 'node:readline';
import { loadImpl } from './impl.ts';
import { answerPrimitive } from './model.ts';

const impl = await loadImpl();
for await (const line of createInterface({ input: process.stdin })) {
  process.stdout.write(`${answerPrimitive(impl, line.trim().split(/\s+/))}\n`);
}
