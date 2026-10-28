#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Hpack/Basic.lean, or to Main.lean
where its description says so. The script copies
the project to a temporary folder, plants one bug at a time, runs
tests/run_tests.py there with a small count and without the oracles,
and records how many failures the tests report. So every failure
counted is the tool disagreeing with the model of RFC 7541; an oracle
that crashes or times out cannot pass for a catch. Every planted bug
must give at least one failure. The unchanged copy must give none. A
bug that stops the executable from building is not a catch: the tests
then give up, and the bug counts as missed. So is any run that gives
up (its record shows `- Failures: 1 (why)`), a run that dies without
writing its record, and one whose exit status does not match the
failures it records.
The tests build only the executable (`lake build hpack`), so a bug
that breaks a proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Hpack/Basic.lean"

# (what the bug does, the line as written, the line with the bug)
BUGS = [
    ("the prefix is off by one: 2^N - 1 is written in the prefix alone",
     "  if i < 2 ^ n - 1 then [(top + i).toUInt8]",
     "  if i < 2 ^ n then [(top + i).toUInt8]"),
    ("the decoder reads the prefix one bit wider",
     "    if b.toNat % 2 ^ n < 2 ^ n - 1 then some (b.toNat % 2 ^ n, bs)",
     "    if b.toNat % 2 ^ (n + 1) < 2 ^ (n + 1) - 1 then some (b.toNat % 2 ^ (n + 1), bs)"),
    ("the decoder keeps the bits above the prefix",
     "    if b.toNat % 2 ^ n < 2 ^ n - 1 then some (b.toNat % 2 ^ n, bs)",
     "    if b.toNat % 2 ^ n < 2 ^ n - 1 then some (b.toNat, bs)"),
    ("non-minimal integers are accepted",
     "    if last = 0 ∧ more ≠ [] then none else some (ofDigits 7 (last :: more), rest)",
     "    if False then none else some (ofDigits 7 (last :: more), rest)"),
    ("the continuation bit is tested as 0x40, not 0x80",
     "    if b.toNat < 128 then some (b.toNat :: acc, bs)",
     "    if b.toNat < 64 then some (b.toNat :: acc, bs)"),
    ("long integers: the first half is shifted by the length of the first half, not the second",
     "        (go fuel (ds.take h) <<< (w * (ds.length - h))) + go fuel (ds.drop h)",
     "        (go fuel (ds.take h) <<< (w * h)) + go fuel (ds.drop h)"),
    ("the encoder writes 128 as a last octet",
     "  if j < 128 then [j.toUInt8] else (j % 128 + 128).toUInt8 :: encodeRest (j / 128)",
     "  if j ≤ 128 then [j.toUInt8] else (j % 128 + 128).toUInt8 :: encodeRest (j / 128)"),
    ("the limit test is < instead of ≤",
     "  | some (i, rest) => if i ≤ max then some (i, rest) else none",
     "  | some (i, rest) => if i < max then some (i, rest) else none"),
    ("EOS is not checked",
     "      if s = 256 then none",
     "      if s = 257 then none"),
    ("padding of 8 bits is allowed",
     "  | [], pending => if pending.length < 8 ∧ pending.all (· == true) then some [] else none",
     "  | [], pending => if pending.length ≤ 8 ∧ pending.all (· == true) then some [] else none"),
    ("padding may hold zeros",
     "  | [], pending => if pending.length < 8 ∧ pending.all (· == true) then some [] else none",
     "  | [], pending => if pending.length < 8 then some [] else none"),
    ("the encoder pads with zeros",
     "  ofBits (bits ++ List.replicate ((8 - bits.length % 8) % 8) true)",
     "  ofBits (bits ++ List.replicate ((8 - bits.length % 8) % 8) false)"),
    ("one Huffman table entry is wrong: the code of ~ ends in e, not d",
     "(0x1ffd, 13)",
     "(0x1ffe, 13)"),
    ("string data one octet short is accepted",
     "      if data.length = len then",
     "      if data.length + 1 ≥ len then"),
    ("the H flag is ignored",
     "        if b.toNat < 128 then some (data, rest.drop len)",
     "        if b.toNat < 256 then some (data, rest.drop len)"),
    ("the Huffman lookup compares bits with the codes one bit longer",
     "  (Array.range 31).map fun l => (indexed codes 0).filter (·.1.length == l)",
     "  (Array.range 31).map fun l => (indexed codes 0).filter (·.1.length == l + 1)"),
    ("a Huffman literal gives the length of the string, not of its encoding",
     "    encodeInt 7 1 d.length ++ d",
     "    encodeInt 7 1 s.length ++ d"),
    ("the static table is indexed from 0",
     "  if i = 0 then none else staticTable[i - 1]?",
     "  if i = 0 then none else staticTable[i]?"),
    ("Main.lean: `intmax` takes any prefix size",
     "  | [\"intmax\", n, m, h] => do\n    let n ← prefixSize n",
     "  | [\"intmax\", n, m, h] => do\n    let n ← decimal n",
     "Main.lean"),
    ("Main.lean: `huffman-decode` exits with 0 when the input does not decode",
     "      | none => IO.eprintln \"not a Huffman encoding\"; return 1",
     "      | none => IO.eprintln \"not a Huffman encoding\"; return 0",
     "Main.lean"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count),
                          "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or m.group(2).strip():
        return None, out  # the run gave up, for example the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=1000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "hpack"
        shutil.copytree(ROOT, copy, symlinks=True,
                        ignore=shutil.ignore_patterns("PLANTED-BUGS.md", "__pycache__"))
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        print(f"none: {n} failures" + (" (did not build or did not finish)" if err else ""),
              flush=True)
        for what, line, bug, *where in BUGS:
            name = where[0] if where else CODE
            code = copy / name
            original = code.read_text(encoding="utf-8")
            if original.count(line) != 1:
                sys.exit(f"{name} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""),
                  flush=True)
            if err:
                print(err[-2000:], flush=True)
    lines = ["# Planted bugs", "",
             "Written by `tests/plant_bugs.py`. Each bug is a change of one line, or two for "
             f"the first `Main.lean` bug, to `{CODE}` unless it names `Main.lean`, tested with `tests/run_tests.py --count {args.count} --no-oracles`, "
             "which builds only the executable and compares it with the model alone. Every bug "
             "must give failures, and the unchanged code none. A bug that does not build, or a "
             "run that gives up or dies, counts as missed.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |"
              for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
