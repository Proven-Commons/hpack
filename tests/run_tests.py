#!/usr/bin/env python3
"""Differential tests: the Lean HPACK integers, Huffman code, string
literals and static table against a model of RFC 7541 and three
implementations.

The tool answers `int`, `intmax`, `encint`, `huffdec`, `huffenc`,
`strdec`, `strenc` and `static` requests (see the header of Main.lean).
Its answers are checked two ways.

1. Against the model, a Python transcription of RFC 7541 that shares
   nothing with the Lean code: `encode_int` and `decode_int` follow the
   pseudocode of section 5.1, `huffman_encode` and `huffman_decode` the
   rules of section 5.2 ("the bitwise concatenation of the codes", EOS,
   padding "strictly longer than 7 bits", padding "not corresponding to
   the most significant bits of the code for the EOS symbol"),
   `decode_string` and `encode_string` the string literal of section
   5.2, and `static_entry` Table 1. The Huffman code is read from the
   "code as bits" column of Appendix B, and the static table from
   Appendix A, of the copy of RFC 7541 in tests/rfc7541.txt, whose
   SHA-256 is checked first; the bits column is checked against the hex
   and length columns, and the code for being prefix-free and complete.
   The model is checked against the examples of Appendix C. Every
   answer must agree.

   One rule is the code's, not the RFC's: `decodeInt` refuses an
   integer whose last continuation octet is 0x00 after another
   continuation octet, an encoding longer than it need be. RFC 7541
   does not require minimal encodings; refusing them is this library's
   choice, stricter than the RFC, and `decode_int` applies the rule
   with `minimal=True`.

2. Against three oracles, on every request each can answer:

   - Python hpack: the `hpack` package, version and wheel hash pinned in
     tests/oracles/python/requirements.txt, installed with
     `pip --require-hashes` into a virtual environment in
     .lake/oracle-python, and driven by tests/oracles/python/oracle.py:
     `decode_integer` and `encode_integer`, `decode_huffman` and
     `HuffmanEncoder`, and `Decoder` and `Encoder` for string literals
     and static entries;
   - Go: package hpack of golang.org/x/net/http2/hpack, at the version
     tests/oracles/go/go.mod pins (go.sum holds its hash), through the
     program there: `HuffmanDecode`, `AppendHuffmanString`, a `Decoder`
     for string literals, static entries and integers with a 5-bit
     prefix (as dynamic table size updates), and an `Encoder` for the
     same integers;
   - nghttp2: the HPACK inflater of libnghttp2 (`nghttp2_hd_inflate_hd2`),
     the version NGHTTP2_PINNED, built against the system library with
     `cc` and tests/oracles/nghttp2/wrapper.c: string literals, Huffman
     strings framed as string literals, static entries, and integers
     with a 5-bit prefix as dynamic table size updates.

   A string literal is read by an oracle as the value of a literal
   header field without indexing with a new name: the block 00, the
   name literal 01 61, then the octets under test. Each oracle says
   which requests it cannot answer (`n/a`). Each has a limit on the
   integers it reads, so none is asked `int`; each is asked `intmax`
   with a limit it can state: Python hpack up to 2^N - 2 + 2^35 (it
   reads at most five continuation octets), Go and nghttp2 up to
   2^32 - 1 (a table size is 32 bits). Every `int` request is also sent
   as `intmax` with each of those limits.

   An oracle that cannot be built or started is left out, and the
   record says so on its `- Oracles left out:` line. A disagreement is
   allowed only where the tool refuses and the oracle answers, for a
   named reason that the model confirms: the model, with the rule the
   oracle reads by, gives the oracle's answer. Each is counted under its
   reason. The one reason is an integer written in more octets than it
   needs, which every oracle reads, within its own limit on continuation
   octets (Python hpack and nghttp2 five, Go nine). Any other
   disagreement is a failure.

Inputs come from a recorded seed, after fixed sets:

- Appendix C: the integers of C.1, and for every representation of
  every header block of C.2 to C.6 each integer and string literal at
  its place in the block (the rest of the block after it), its
  encoding, each static index, and each Huffman string;
- integers: every prefix size 1 to 8 with every value from 0 to
  2^N + 300, values around every power of two up to 2^70 and where the
  encoding gains an octet, and the oracles' limits; each encoded with
  random bits above the prefix and decoded with random octets after it,
  with every proper prefix of its encoding, and with limits just below
  and at the value; every value of the bits above the prefix for some
  values; 1 to 12 extra zero continuation octets;
- Huffman: every input of 0, 1 and 2 octets; the encoding of every
  octet, with zeros or eight more ones as padding; EOS in several
  places;
- string literals: lengths 0, 1, 126 to 129 and 300 (120 over all 256
  octets), raw and Huffman, whole, cut short, with the H flag flipped
  and with non-minimal lengths; literals of zero to three octets;
  literals whose Huffman data holds EOS; lengths up to 2^100 with
  three octets of data;
- static indices 0 to 100 and some far past the table;
- long inputs: integers of 17 to 1,001 continuation octets, one of
  100,002 octets under a limit, string lengths written in 100,002
  octets, and strings of about 100 KB, one of every octet value and one
  of 30-bit codes, encoded and decoded, raw and Huffman;
- random strings, over all 256 octets and over printable ASCII, up to
  120 and 300 octets: their Huffman encoding and its decoding, the
  encoding with a bit flipped, eight more ones of padding, a zero in
  the padding, padding of zeros, EOS inserted, the last octet cut; raw
  and Huffman string literals of them with random octets after, cut
  short, with the H flag flipped, and with a non-minimal length when it
  is 127 or more;
- random octet strings read as integers with every prefix size;
- malformed requests, which the tool must answer with `error`, and odd
  but well-formed ones (leading zeros, numbers past 64 bits);
- the command-line modes `huffman-encode`, `huffman-decode` and
  `string-decode`, on input that decodes, input that does not, and
  malformed hex, and wrong arguments: what each run prints on standard
  output and its exit status.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles]

`--count` is the number of random strings; half as many random octet
strings are read as integers. `--no-oracles` leaves every oracle out and
compares the tool with the model alone, as tests/plant_bugs.py does.
The script builds the executable and the oracles first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
"""

import argparse
import hashlib
import os
import random
import re
import subprocess
import sys
import threading
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "hpack"
TESTS = ROOT / "tests"
RFC = TESTS / "rfc7541.txt"
# https://www.rfc-editor.org/rfc/rfc7541.txt
RFC_SHA256 = "2239d7f8fb839b69ae2e928e685559b11376888269f131512197a0e3bacf7f7a"
ORACLES = TESTS / "oracles"
PY_SRC = ORACLES / "python"
PY_ENV = ROOT / ".lake" / "oracle-python"
GO_SRC = ORACLES / "go"
GO_EXE = ROOT / ".lake" / "oracle-go" / "go-oracle"
NGHTTP2_SRC = ORACLES / "nghttp2"
NGHTTP2_EXE = ROOT / ".lake" / "oracle-nghttp2" / "nghttp2-oracle"
NGHTTP2_PINNED = "1.59.0"
RESULTS = TESTS / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600
# The requests are split among this many `hpack serve` processes.
JOBS = max(1, min(4, os.cpu_count() or 1))

# ---------------------------------------------------------------------
# RFC 7541, read from tests/rfc7541.txt.


class RFCError(Exception):
    pass


def rfc_lines():
    """The lines of the RFC without its page breaks: form feeds, and the
    footer and header lines of each page."""
    lines = []
    for line in RFC.read_text(encoding="ascii").replace("\f", "").split("\n"):
        if re.match(r"^Peon & Ruellan\s+Standards Track\s+\[Page \d+\]$", line):
            continue
        if re.match(r"^RFC 7541\s+HPACK\s+May 2015$", line):
            continue
        lines.append(line)
    return lines


def appendix(lines, letter, following):
    """The lines of Appendix `letter`, up to the heading `following`."""
    start = next(i for i, l in enumerate(lines) if l.startswith(f"Appendix {letter}."))
    end = next(i for i, l in enumerate(lines) if i > start and l.startswith(following))
    return lines[start:end]


def parse_huffman(lines):
    """Appendix B: the code of each symbol, 0 to 255 and EOS (256), as a
    string of bits, from the column "code as bits aligned to MSB". Each
    is checked against the columns "code as hex aligned to LSB" and "len
    in bits", and the code for being prefix-free and complete."""
    row = re.compile(r"^\s+(?:'.' |EOS )?\(\s*(\d+)\)\s+((?:\|[01]+)+)\s+([0-9a-f]+)"
                     r"\s+\[\s*(\d+)\]\s*$")
    codes = {}
    for line in appendix(lines, "B", "Appendix C."):
        m = row.match(line)
        if not m:
            continue
        sym, bits = int(m.group(1)), m.group(2).replace("|", "")
        if sym in codes:
            raise RFCError(f"Appendix B lists symbol {sym} twice")
        if len(bits) != int(m.group(4)) or int(bits, 2) != int(m.group(3), 16):
            raise RFCError(f"Appendix B: the columns of symbol {sym} disagree")
        codes[sym] = bits
    if sorted(codes) != list(range(257)):
        raise RFCError(f"Appendix B: {len(codes)} symbols read, not 257")
    ordered = sorted(codes.values())
    for a, b in zip(ordered, ordered[1:]):
        if b.startswith(a):
            raise RFCError(f"Appendix B: {a} is a prefix of {b}")
    if sum(Fraction(1, 2 ** len(c)) for c in ordered) != 1:
        raise RFCError("Appendix B: the code is not complete")
    if codes[256] != "1" * 30:
        raise RFCError("Appendix B: EOS is not 30 ones")
    return [codes[s] for s in range(257)]


def parse_static(lines):
    """Appendix A, Table 1: (name, value) in index order from 1."""
    row = re.compile(r"^\s+\| (\d+)\s+\| (\S+)\s+\| (.*?)\s*\|\s*$")
    table = []
    for line in appendix(lines, "A", "Appendix B."):
        m = row.match(line)
        if m:
            if int(m.group(1)) != len(table) + 1:
                raise RFCError(f"Appendix A: index {m.group(1)} out of order")
            table.append((m.group(2).encode("ascii"), m.group(3).encode("ascii")))
    if len(table) != 61:
        raise RFCError(f"Appendix A: {len(table)} entries, not 61")
    return table


def parse_examples(lines):
    """Appendix C.2 to C.6: for each example, its section, the octets of
    its "Hex dump of encoded data" and its "Decoded header list"."""
    examples, cur, mode, section = [], None, None, None
    hexrow = re.compile(r"^   ([0-9a-f]{2,4}(?: [0-9a-f]{2,4})*)\s+\|")
    for line in appendix(lines, "C", "Acknowledgments"):
        m = re.match(r"^(C\.\d\.\d)\.\s", line)
        if m:
            section, mode = m.group(1), None
            continue
        if line and not line.startswith(" "):
            mode = None
            continue
        text = line.strip()
        if text == "Hex dump of encoded data:":
            cur = {"section": section, "block": b"", "headers": []}
            examples.append(cur)
            mode = "hex"
        elif text == "Decoded header list:":
            mode = "list"
        elif mode == "hex" and text:
            m = hexrow.match(line)
            if not m:
                mode = None
                continue
            cur["block"] += bytes.fromhex(m.group(1).replace(" ", ""))
        elif mode == "list" and text:
            k = text.find(": ", 1)
            cur["headers"].append((text[:k].encode("ascii"), text[k + 2:].encode("ascii")))
    if len(examples) != 16:
        raise RFCError(f"Appendix C: {len(examples)} examples read, not 16")
    return examples


def read_rfc():
    digest = hashlib.sha256(RFC.read_bytes()).hexdigest()
    if digest != RFC_SHA256:
        raise RFCError(f"{RFC.name} has SHA-256 {digest}, not {RFC_SHA256}")
    lines = rfc_lines()
    return parse_huffman(lines), parse_static(lines), parse_examples(lines)


HUFFMAN, STATIC, EXAMPLES = None, None, None
SYMBOL_OF = {}

# ---------------------------------------------------------------------
# The model: RFC 7541.

NONMINIMAL = "written in more octets than it needs"


def encode_int(n, high, i):
    """Section 5.1, "Pseudocode to represent an integer I", with `high`
    in the 8 - N bits of the first octet above the prefix:

        if I < 2^N - 1, encode I on N bits
        else
            encode (2^N - 1) on N bits
            I = I - (2^N - 1)
            while I >= 128
                 encode (I % 128 + 128) on 8 bits
                 I = I / 128
            encode I on 8 bits
    """
    if i < 2 ** n - 1:
        return bytes([high << n | i])
    out = [high << n | (2 ** n - 1)]
    i -= 2 ** n - 1
    while i >= 128:
        out.append(i % 128 + 128)
        i //= 128
    out.append(i)
    return bytes(out)


def decode_int(n, data, minimal=True, max_cont=None, top=None):
    """Section 5.1, "Pseudocode to decode an integer I":

        decode I from the next N bits
        if I < 2^N - 1, return I
        else
            M = 0
            repeat
                B = next octet
                I = I + (B & 127) * 2^M
                M = M + 7
            while B & 128 == 128
            return I

    Returns ((I, the octets after it), None) or (None, why). With
    `minimal`, an encoding whose last continuation octet is 0 after
    another continuation octet is refused (the code's rule, see above).
    `max_cont` is the most continuation octets read, and `top` the
    largest value accepted: the "implementation limits" of section 5.1
    that an oracle has."""
    if not data:
        return None, "the input ends first"
    i = data[0] & (2 ** n - 1)
    pos = 1
    if i == 2 ** n - 1:
        # The terms (B & 127) * 2^M of the loop, kept and added up at the
        # end in one step: adding them one at a time to a growing number
        # takes time quadratic in the number of octets.
        groups = []
        while True:
            if pos == len(data):
                return None, "the input ends first"
            if max_cont is not None and pos > max_cont:
                return None, "more continuation octets than the limit"
            b = data[pos]
            pos += 1
            groups.append(b & 127)
            if b & 128 != 128:
                break
        i += int("".join(f"{g:07b}" for g in reversed(groups)), 2)
        if minimal and pos > 2 and data[pos - 1] == 0:
            return None, NONMINIMAL
    if top is not None and i > top:
        return None, "above the limit"
    return (i, data[pos:]), None


def bits_of(data):
    return "".join(f"{b:08b}" for b in data)


def octets_of(bits):
    assert len(bits) % 8 == 0
    return int(bits, 2).to_bytes(len(bits) // 8, "big") if bits else b""


def huffman_bits(s):
    """Section 5.2: "the bitwise concatenation of the codes corresponding
    to each octet of the string literal"."""
    return "".join(HUFFMAN[c] for c in s)


def huffman_encode(s):
    """The codes, then padding: "the most significant bits of the code
    corresponding to the EOS (end-of-string) symbol", to the next octet
    boundary. EOS is 30 ones."""
    bits = huffman_bits(s)
    return octets_of(bits + HUFFMAN[256][:(8 - len(bits) % 8) % 8])


def huffman_decode(d):
    """The octets whose Huffman encoding is `d`: (octets, None), or
    (None, why) for what section 5.2 says "MUST be treated as a decoding
    error"."""
    out, pending = bytearray(), ""
    for bit in bits_of(d):
        pending += bit
        sym = SYMBOL_OF.get(pending)
        if sym is not None:
            # "A Huffman-encoded string literal containing the EOS
            # symbol MUST be treated as a decoding error."
            if sym == 256:
                return None, "EOS"
            out.append(sym)
            pending = ""
    # "A padding strictly longer than 7 bits MUST be treated as a
    # decoding error."
    if len(pending) > 7:
        return None, "padding over 7 bits"
    # "A padding not corresponding to the most significant bits of the
    # code for the EOS symbol MUST be treated as a decoding error."
    if pending != HUFFMAN[256][:len(pending)]:
        return None, "padding not all ones"
    return bytes(out), None


def encode_string(h, s):
    """Section 5.2: the H flag, the length of the string data as an
    integer with a 7-bit prefix, and the string data: the octets
    themselves, or with H = 1 their Huffman encoding."""
    data = huffman_encode(s) if h else bytes(s)
    return encode_int(7, h, len(data)) + data


def decode_string(data, minimal=True, max_cont=None, top=None):
    """The string literal at the start of `data`: ((octets, the octets
    after it), None) or (None, why). `minimal`, `max_cont` and `top`
    apply to its length, as for `decode_int`."""
    r, why = decode_int(7, data, minimal, max_cont, top)
    if r is None:
        return None, f"the length: {why}"
    length, rest = r
    if length > len(rest):
        return None, "the input ends before the string data"
    s = rest[:length]
    if data[0] & 0x80:
        s, why = huffman_decode(s)
        if s is None:
            return None, f"the Huffman data: {why}"
    return (bytes(s), rest[length:]), None


def static_entry(i):
    """Appendix A: the entry at index i, counting from 1."""
    if 1 <= i <= len(STATIC):
        return STATIC[i - 1], None
    return None, "index 0" if i == 0 else "an index past the table"


def model(op, args):
    """The model's answer to a request, and why it refuses, or None."""
    if op == "int":
        return decode_int(*args)
    if op == "intmax":
        n, top, data = args
        return decode_int(n, data, top=top)
    if op == "encint":
        return encode_int(*args), None
    if op == "huffdec":
        return huffman_decode(*args)
    if op == "huffenc":
        return huffman_encode(*args), None
    if op == "strdec":
        return decode_string(*args)
    if op == "strenc":
        return encode_string(*args), None
    return static_entry(*args)


# ---------------------------------------------------------------------
# Requests and answers, in the form of `hpack serve`.

def hx(data):
    return bytes(data).hex() or "-"


def request(op, args):
    if op == "int":
        return f"int {args[0]} {hx(args[1])}"
    if op == "intmax":
        return f"intmax {args[0]} {args[1]} {hx(args[2])}"
    if op == "encint":
        return f"encint {args[0]} {args[1]} {args[2]}"
    if op == "strenc":
        return f"strenc {args[0]} {hx(args[1])}"
    if op == "static":
        return f"static {args[0]}"
    return f"{op} {hx(args[0])}"


def render(op, answer):
    """An answer as `hpack serve` writes it."""
    if answer is None:
        return "FAIL"
    if op in ("int", "intmax"):
        return f"OK {answer[0]} {hx(answer[1])}"
    if op in ("strdec", "static"):
        return f"OK {hx(answer[0])} {hx(answer[1])}"
    return f"OK {hx(answer)}"


def model_line(raw):
    """The answer to a request line, as sent with its line ending, as
    Main.lean's header describes the protocol: the line ends in LF or
    CR LF; `error` for a malformed request, else the model's answer."""
    line = raw
    if line.endswith("\n"):
        line = line[:-1]
        if line.endswith("\r"):
            line = line[:-1]
    parts = line.split(" ")
    op, fields = parts[0], parts[1:]

    def octets(f):
        if f == "-":
            return b""
        if f == "" or len(f) % 2 or any(c not in "0123456789abcdef" for c in f):
            raise ValueError
        return bytes.fromhex(f)

    def decimal(f):
        if f == "" or any(c not in "0123456789" for c in f):
            raise ValueError
        return int(f)

    def prefix(f):
        n = decimal(f)
        if not 1 <= n <= 8:
            raise ValueError
        return n

    shapes = {"int": (prefix, octets), "intmax": (prefix, decimal, octets),
              "encint": (prefix, decimal, decimal), "huffdec": (octets,), "huffenc": (octets,),
              "strdec": (octets,), "strenc": (decimal, octets), "static": (decimal,)}
    if op not in shapes or len(fields) != len(shapes[op]):
        return "error"
    try:
        args = tuple(read(f) for read, f in zip(shapes[op], fields))
    except ValueError:
        return "error"
    if op == "encint" and args[1] >= 2 ** (8 - args[0]):
        return "error"
    if op == "strenc" and fields[0] not in ("0", "1"):
        return "error"
    return render(op, model(op, args)[0])


# ---------------------------------------------------------------------
# Running a program over request lines.

def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def run_parallel(cmd, lines, jobs):
    """`run_lines` over `jobs` processes, each given a run of the lines
    in order; the answers in order, and the problems."""
    size = -(-len(lines) // jobs) if lines else 0
    chunks = [lines[k:k + size] for k in range(0, len(lines), size)] if size else [[]]
    results = [None] * len(chunks)

    def one(k):
        results[k] = run_lines(cmd, chunks[k])

    threads = [threading.Thread(target=one, args=(k,)) for k in range(len(chunks))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    answers, problems = [], []
    for chunk, (got, problem) in zip(chunks, results):
        if problem:
            problems.append(problem)
        if len(got) != len(chunk):
            problems.append(f"{len(got)} answers for {len(chunk)} requests")
            got = (got + [""] * len(chunk))[:len(chunk)]
        answers += got
    return answers, problems


# ---------------------------------------------------------------------
# The oracles. Each setup returns an object with `name`, `version` and
# `answers(lines)`, or raises OracleUnavailable.

class OracleUnavailable(Exception):
    pass


class ProcessOracle:
    def __init__(self, name, version, cmd):
        self.name, self.version, self.cmd = name, version, cmd

    def answers(self, lines):
        got, problem = run_lines(self.cmd, lines)
        if problem or len(got) != len(lines):
            raise RuntimeError(f"{self.name} oracle: "
                               f"{problem or f'{len(got)} answers for {len(lines)} requests'}")
        return got


def first_line(cmd, cwd=None):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300, cwd=cwd)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


def setup_python():
    req = (PY_SRC / "requirements.txt").read_text(encoding="utf-8")
    m = re.search(r"^hpack==(\S+) --hash=sha256:([0-9a-f]{64})\s*$", req, re.M)
    if not m:
        raise OracleUnavailable("tests/oracles/python/requirements.txt pins no hpack wheel")
    pinned, digest = m.group(1), m.group(2)
    py = PY_ENV / "bin" / "python"
    stamp = PY_ENV / "requirements.txt"

    def installed():
        return first_line([str(py), "-I", "-c", "import hpack; print(hpack.__version__)"])

    if not (stamp.exists() and stamp.read_text(encoding="utf-8") == req and installed() == pinned):
        try:
            subprocess.run([sys.executable, "-m", "venv", "--clear", str(PY_ENV)], check=True,
                           capture_output=True, timeout=BUILD_TIMEOUT)
            # --require-hashes installs only the wheel whose SHA-256
            # requirements.txt names.
            subprocess.run([str(py), "-m", "pip", "install", "--quiet", "--disable-pip-version-check",
                            "--require-hashes", "--no-deps", "--only-binary", ":all:", "-r",
                            str(PY_SRC / "requirements.txt")], check=True, capture_output=True,
                           timeout=BUILD_TIMEOUT)
        except (OSError, subprocess.SubprocessError) as e:
            raise OracleUnavailable(f"`pip install --require-hashes` did not install it: {e}")
        stamp.write_text(req, encoding="utf-8")
    version = installed()
    if version != pinned:
        raise OracleUnavailable(f"hpack {version} is installed, not {pinned}")
    return ProcessOracle("Python hpack", f"hpack {version} (python-hyper), the wheel pinned by "
                         f"SHA-256 {digest}, on {first_line([str(py), '-I', '--version'])}",
                         [str(py), "-I", str(PY_SRC / "oracle.py")])


def setup_go():
    GO_EXE.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, GOFLAGS="-mod=readonly", CGO_ENABLED="0", GOTOOLCHAIN="local")
    try:
        subprocess.run(["go", "build", "-o", str(GO_EXE), "."], cwd=GO_SRC, check=True, env=env,
                       capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`go build` did not build it: {e}")
    mod = re.search(r"^require golang.org/x/net (\S+)",
                    (GO_SRC / "go.mod").read_text(encoding="utf-8"), re.M)
    sums = re.search(r"^golang.org/x/net \S+ (h1:\S+)",
                     (GO_SRC / "go.sum").read_text(encoding="utf-8"), re.M)
    return ProcessOracle("Go", f"package hpack of golang.org/x/net/http2 "
                         f"{mod.group(1) if mod else '?'} ({sums.group(1) if sums else '?'}), "
                         f"built with {first_line(['go', 'version'])}", [str(GO_EXE)])


def setup_nghttp2():
    NGHTTP2_EXE.parent.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.run(["cc", "-O2", "-o", str(NGHTTP2_EXE), str(NGHTTP2_SRC / "wrapper.c"),
                        "-lnghttp2"], check=True, capture_output=True, timeout=BUILD_TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        raise OracleUnavailable(f"`cc` did not build the wrapper against libnghttp2 (is "
                                f"libnghttp2-dev installed?): {e}")
    got, problem = run_lines([str(NGHTTP2_EXE)], ["version\n"], timeout=60)
    version = got[0][3:] if got and got[0].startswith("OK ") and not problem else "unknown"
    if version != NGHTTP2_PINNED:
        raise OracleUnavailable(f"libnghttp2 {version} is installed, not {NGHTTP2_PINNED}")
    package = first_line(["dpkg-query", "-W", "-f", "${Package} ${Version}\n", "libnghttp2-14"])
    return ProcessOracle("nghttp2", f"libnghttp2 {version}, the HPACK inflater "
                         f"`nghttp2_hd_inflate_hd2`"
                         + (f" (Debian package {package})" if package != "unknown" else "")
                         + f", through `tests/oracles/nghttp2/wrapper.c` compiled with "
                         f"{first_line(['cc', '--version'])}", [str(NGHTTP2_EXE)])


ORACLE_SETUPS = [("Python hpack", setup_python), ("Go", setup_go), ("nghttp2", setup_nghttp2)]

# The limits the oracles are asked under (see the top of this file): the
# `intmax` limits for a prefix size N, and the most continuation octets
# each reads.
GO_LIMIT = 2 ** 32 - 1


def oracle_limits(n):
    return sorted({2 ** n - 2 + 2 ** 35} | ({GO_LIMIT} if n == 5 else set()))


MAX_CONT = {"Python hpack": 5, "Go": 9, "nghttp2": 5}
# nghttp2 refuses a string longer than NGHTTP2_HD_MAX_NV.
MAX_STRING = {"nghttp2": 65536}

REASONS = {
    "Python hpack": "decode_integer reads an integer written in more octets than it needs "
                    "(a last continuation octet 0 after another), up to five continuation octets",
    "Go": "readVarInt reads an integer written in more octets than it needs (a last "
          "continuation octet 0 after another), up to nine continuation octets",
    "nghttp2": "the inflater reads an integer written in more octets than it needs (a last "
               "continuation octet 0 after another), up to five continuation octets",
}


def oracle_model(oracle, op, args):
    """The model's answer with the rule the oracle reads integers by: no
    minimality, and its own limits."""
    if op == "intmax":
        n, top, data = args
        return decode_int(n, data, minimal=False, max_cont=MAX_CONT[oracle], top=top)[0]
    if op == "strdec":
        return decode_string(args[0], minimal=False, max_cont=MAX_CONT[oracle],
                             top=MAX_STRING.get(oracle))[0]
    return None


# nghttp2 refuses a header field whose name and value together pass
# 65,536 octets: NGHTTP2_HD_MAX_NV in its lib/nghttp2_hd.h. The name is
# one octet here.
NGHTTP2_MAX_NV = 65536


def beyond_limit(oracle, op, answer):
    """Whether a request is past a limit the oracle has on what it gives
    back, so that its refusal is not compared: a value over 65,535
    octets for nghttp2."""
    if oracle == "nghttp2" and op in ("strdec", "huffdec") and answer is not None:
        value = answer[0] if op == "strdec" else answer
        return 1 + len(value) > NGHTTP2_MAX_NV
    return False


def difference_reason(oracle, op, args, why, got, theirs):
    """The named reason the oracle's answer differs from the tool's,
    confirmed by the model, or None. The one reason is an integer that
    every oracle reads and the code refuses, so it can excuse only a
    disagreement where the tool refused and the oracle answered."""
    if got != "FAIL" or not theirs.startswith("OK "):
        return None
    if op not in ("intmax", "strdec") or why is None or NONMINIMAL not in why:
        return None
    if render(op, oracle_model(oracle, op, args)) != theirs:
        return None
    return REASONS[oracle] + (", in a string length" if op == "strdec" else "")


# ---------------------------------------------------------------------
# The fixed sets.

def walk(block, table, size_max):
    """Read a header block as section 6 lays it out, with the model's
    integers and string literals and a dynamic table (sections 2.3 and
    4): the header list, the block written again from what was read, and
    the requests to ask at each step."""
    headers, again, asks = [], [], []
    pos = 0

    def integer(n):
        nonlocal pos
        r, why = decode_int(n, block[pos:])
        if r is None:
            raise RFCError(f"an integer the model refuses: {why}")
        high = block[pos] >> n
        asks.extend([("int", (n, block[pos:])), ("encint", (n, high, r[0]))])
        again.append(encode_int(n, high, r[0]))
        pos = len(block) - len(r[1])
        return r[0]

    def literal():
        nonlocal pos
        r, why = decode_string(block[pos:])
        if r is None:
            raise RFCError(f"a string literal the model refuses: {why}")
        h = block[pos] >> 7
        asks.extend([("strdec", (block[pos:],)), ("strenc", (h, r[0]))])
        if h:
            length = decode_int(7, block[pos:])[0]
            asks.extend([("huffdec", (length[1][:length[0]],)), ("huffenc", (r[0],))])
        again.append(encode_string(h, r[0]))
        pos = len(block) - len(r[1])
        return r[0]

    def entry(i):
        return STATIC[i - 1] if i <= len(STATIC) else table[i - len(STATIC) - 1]

    def evict(room):
        while table and sum(32 + len(a) + len(b) for a, b in table) > room:
            table.pop()

    while pos < len(block):
        b = block[pos]
        if b & 0x80:  # 6.1, indexed header field
            i = integer(7)
            asks.append(("static", (i,)))
            headers.append(entry(i))
        elif b & 0x20 and not b & 0x40:  # 6.3, dynamic table size update
            size_max = integer(5)
            evict(size_max)
        else:  # 6.2.1 with incremental indexing (01), 6.2.2 without (0000), 6.2.3 never (0001)
            i = integer(6 if b & 0x40 else 4)
            name = entry(i)[0] if i else literal()
            value = literal()
            headers.append((name, value))
            if b & 0x40:
                size = 32 + len(name) + len(value)
                evict(size_max - size)
                if size <= size_max:
                    table.insert(0, (name, value))
    return headers, b"".join(again), asks


# C.1: 10 and 1337 with a 5-bit prefix, and 42 with an 8-bit one.
C1 = [((5, 10), bytes([0x0a])), ((5, 1337), bytes([0x1f, 0x9a, 0x0a])), ((8, 42), bytes([0x2a]))]


def appendix_c():
    """The requests of Appendix C, and how many integers of C.1 and
    header blocks of C.2 to C.6 the model reads as the RFC does."""
    asks, blocks_right, ints_right = [], 0, 0
    for (n, v), enc in C1:
        asks += [("encint", (n, 0, v)), ("int", (n, enc))]
        ints_right += encode_int(n, 0, v) == enc and decode_int(n, enc)[0] == (v, b"")
    tables = {}
    for ex in EXAMPLES:
        group = ex["section"][:3]
        size_max = 256 if group in ("C.5", "C.6") else 4096
        table = [] if group == "C.2" else tables.setdefault(group, [])
        headers, again, more = walk(ex["block"], table, size_max)
        asks += more
        blocks_right += headers == ex["headers"] and again == ex["block"]
    return asks, ints_right, blocks_right


def bounded(values):
    return sorted(v for v in values if v >= 0)


def int_values(n):
    """Every value from 0 to 2^N + 300, values around every power of two
    up to 2^70, around each value where the encoding gains an octet, and
    around the oracles' limits."""
    vals = set(range(2 ** n + 301))
    for k in range(71):
        vals.update(2 ** k + d for d in (-2, -1, 0, 1, 2))
    for j in range(1, 11):
        vals.update(2 ** n - 1 + 128 ** j + d for d in (-1, 0, 1))
    for top in oracle_limits(n):
        vals.update(top + d for d in (-1, 0, 1))
    return bounded(vals)


def with_limits(label, n, data, value=None):
    """`int N data`, and `intmax` with limits just below and at the
    value. (`inputs` adds the oracles' limits to every `int`.)"""
    yield (label, "int", (n, data))
    if value is not None:
        for top in (value - 1, value):
            if top >= 0:
                yield (label + ", with a limit", "intmax", (n, top, data))


def extra_zeros(enc, z):
    """The encoding with z more continuation octets of value 0: the last
    continuation octet gets its top bit, then 80 z - 1 times, then 00."""
    return enc[:-1] + bytes([enc[-1] | 0x80]) + b"\x80" * (z - 1) + b"\x00"


def integer_sets():
    rng = random.Random(1)
    for n in range(1, 9):
        highs = 2 ** (8 - n)
        for v in int_values(n):
            enc = encode_int(n, rng.randrange(highs), v)
            yield ("integer", "encint", (n, rng.randrange(highs), v))
            if n == 5:  # as a dynamic table size update writes it
                yield ("integer", "encint", (n, 1, v))
            tail = bytes(rng.randrange(256) for _ in range(rng.choice([0, 0, 1, 2])))
            yield from with_limits("integer", n, enc + tail, v)
            for k in range(1, len(enc)):
                yield from with_limits("integer, cut short", n, enc[:k])
        some = [0, 1, 2 ** n - 2, 2 ** n - 1, 2 ** n, 2 ** n + 126, 2 ** n + 127, 1337,
                2 ** 32 - 1, 2 ** 64]
        for v in bounded(some):
            for high in range(highs):
                yield ("integer, every high-bits value", "encint", (n, high, v))
                yield ("integer, every high-bits value", "int", (n, encode_int(n, high, v)))
        zeros = [2 ** n - 1, 2 ** n, 2 ** n + 126, 2 ** n + 127, 2 ** n + 128, 1337, 2 ** 21,
                 2 ** 32 - 1, 2 ** 35, 2 ** 63]
        for v in zeros:
            enc = encode_int(n, rng.randrange(highs), v)
            for z in range(1, 13):
                data = extra_zeros(enc, z) + bytes(rng.randrange(256)
                                                   for _ in range(rng.choice([0, 1])))
                yield from with_limits("integer, extra zero octets", n, data, v)


def huffman_sets():
    for a in [None] + list(range(256)):
        if a is None:
            yield ("Huffman, 0 to 2 octets", "huffdec", (b"",))
            continue
        yield ("Huffman, 0 to 2 octets", "huffdec", (bytes([a]),))
        for b in range(256):
            yield ("Huffman, 0 to 2 octets", "huffdec", (bytes([a, b]),))
    yield ("Huffman, every octet", "huffenc", (b"",))
    for c in range(256):
        bits = HUFFMAN[c]
        pad = (8 - len(bits) % 8) % 8
        yield ("Huffman, every octet", "huffenc", (bytes([c]),))
        yield ("Huffman, every octet", "huffdec", (octets_of(bits + "1" * pad),))
        if pad:
            yield ("Huffman, padding of zeros", "huffdec", (octets_of(bits + "0" * pad),))
        yield ("Huffman, padding extended", "huffdec", (octets_of(bits + "1" * (pad + 8)),))
    eos = HUFFMAN[256]
    for bits in [eos + "11", eos + "00", HUFFMAN[ord("a")] + eos + "1",
                 eos + HUFFMAN[ord("a")] + "111", "1" * 7, "1" * 8, "1" * 16, "1" * 24,
                 "1" * 29 + "0" + "11", "0" * 8, "1" * 32, "1" * 40]:
        bits += "1" * ((8 - len(bits) % 8) % 8)
        yield ("Huffman, EOS and ones", "huffdec", (octets_of(bits),))


def string_cases(label, h, s, rng, trailing=True):
    """A literal of s: whole with random octets after, cut short, with
    the H flag flipped, and with a non-minimal length when it can have
    one."""
    lit = encode_string(h, s)
    tail = bytes(rng.randrange(256) for _ in range(rng.choice([0, 0, 1, 3]))) if trailing else b""
    yield (label, "strdec", (lit + tail,))
    if len(lit) > 1:
        yield (label + ", cut short", "strdec", (lit[:-1],))
        yield (label + ", cut short", "strdec", (lit[:rng.randrange(1, len(lit))],))
    yield (label + ", H flipped", "strdec", (bytes([lit[0] ^ 0x80]) + lit[1:] + tail,))
    length, data = decode_int(7, lit)[0]
    if length >= 127:
        for z in (1, 2, 5, 9):
            yield (label + ", non-minimal length", "strdec",
                   (extra_zeros(encode_int(7, h, length), z) + data + tail,))


def string_sets():
    rng = random.Random(2)
    ascii_ = bytes(range(32, 127))
    for n in (0, 1, 126, 127, 128, 129, 300):
        for alphabet in (ascii_, bytes(range(256))):
            m = 120 if n == 300 and len(alphabet) == 256 else n
            s = bytes(rng.choice(alphabet) for _ in range(m))
            for h in (0, 1):
                yield ("string, edge", "strenc", (h, s))
                yield from string_cases("string, edge", h, s, rng)
    for lit in [b"", b"\x00", b"\x80", b"\x7f", b"\xff", b"\x7f\x00", b"\xff\x00",
                b"\x7f\x80\x00", b"\x01", b"\x81", b"\x81\x1f", b"\x81\xff", b"\x02a"]:
        yield ("string, edge", "strdec", (lit,))


def more_string_sets():
    """Literals whose Huffman data holds EOS, and lengths far past the
    data."""
    eos = HUFFMAN[256]
    for bits in [eos, HUFFMAN[ord("a")] + eos, eos + HUFFMAN[ord("a")]]:
        bits += "1" * ((8 - len(bits) % 8) % 8)
        d = octets_of(bits)
        yield ("string, Huffman data holding EOS", "strdec", (encode_int(7, 1, len(d)) + d,))
    for length in (2 ** 16, 2 ** 32, 2 ** 64, 2 ** 100):
        for h in (0, 1):
            yield ("string, length far past the data", "strdec",
                   (encode_int(7, h, length) + b"abc",))


def long_sets():
    """Long inputs, which the tool must answer in time linear in their
    length: integers with many continuation octets, string lengths
    written in 100,000 octets, and strings of about 100 KB, among them
    every octet value and the 30-bit codes."""
    for k in (17, 33, 100, 1001):
        yield ("long integer", "int", (5, bytes([0x1f] + [0xff] * (k - 1) + [0x01])))
    big = bytes([0x1f] + [0xff] * 100_000 + [0x01])
    yield ("long integer", "intmax", (5, 2 ** 32 - 1, big))
    yield ("long string length", "strdec", (bytes([0x7f] + [0xff] * 100_000 + [0x01]),))
    yield ("long string length", "strdec", (bytes([0xff] + [0xff] * 100_000 + [0x01]),))
    every = bytes(range(256)) * 400
    long30 = bytes([10, 13, 22]) * 30_000
    for s in (every, long30):
        yield ("long string", "huffenc", (s,))
        yield ("long string", "huffdec", (huffman_encode(s),))
        for h in (0, 1):
            yield ("long string", "strenc", (h, s))
            yield ("long string", "strdec", (encode_string(h, s) + b"\x01",))


def static_sets():
    for i in list(range(101)) + [127, 128, 255, 256, 2 ** 32, 2 ** 64, 10 ** 30]:
        yield ("static", "static", (i,))


def random_string(rng):
    """Random octets: over printable ASCII up to 300, or over all 256
    octets up to 120."""
    full = rng.random() < 0.5
    r = rng.random()
    if r < 0.25:
        n = rng.randint(0, 4)
    elif r < 0.7:
        n = rng.randint(5, 24)
    elif r < 0.93:
        n = rng.randint(25, 80)
    else:
        n = rng.randint(81, 120 if full else 300)
    if full:
        return bytes(rng.randrange(256) for _ in range(n))
    return bytes(rng.randrange(32, 127) for _ in range(n))


def huffman_mutations(rng, s):
    """The encoding of s with a bit flipped, eight more ones of padding,
    a zero in the padding, padding of zeros, EOS inserted at a symbol
    boundary, and its last octet cut."""
    bits = huffman_bits(s)
    pad = (8 - len(bits) % 8) % 8
    enc = octets_of(bits + "1" * pad)
    if enc:
        k = rng.randrange(len(enc) * 8)
        flipped = bytearray(enc)
        flipped[k // 8] ^= 0x80 >> (k % 8)
        yield ("Huffman, bit flipped", "huffdec", (bytes(flipped),))
        yield ("Huffman, last octet cut", "huffdec", (enc[:-1],))
    yield ("Huffman, padding extended", "huffdec", (octets_of(bits + "1" * (pad + 8)),))
    if pad:
        k = rng.randrange(pad)
        yield ("Huffman, a zero in the padding", "huffdec",
               (octets_of(bits + "1" * k + "0" + "1" * (pad - k - 1)),))
        yield ("Huffman, padding of zeros", "huffdec", (octets_of(bits + "0" * pad),))
    k = rng.randint(0, len(s))
    with_eos = huffman_bits(s[:k]) + HUFFMAN[256] + huffman_bits(s[k:])
    yield ("Huffman, EOS inserted", "huffdec",
           (octets_of(with_eos + "1" * ((8 - len(with_eos) % 8) % 8)),))


def random_int_data(rng):
    n = rng.randint(1, 8)
    data = bytearray()
    length = rng.randint(0, 12)
    for k in range(length):
        r = rng.random()
        if k == 0 and r < 0.7:
            data.append(rng.randrange(256) | (2 ** n - 1))
        elif r < 0.2:
            data.append(0x80)
        elif r < 0.35:
            data.append(0x00)
        elif r < 0.45:
            data.append(0xff)
        elif r < 0.75:
            data.append(rng.randrange(128, 256))
        else:
            data.append(rng.randrange(256))
    return n, bytes(data)


def inputs(seed, count):
    """(label, op, args) for every request: those of `requests`, and
    each `int` again as `intmax` with each oracle's limit."""
    for label, op, a in requests(seed, count):
        yield (label, op, a)
        if op == "int":
            for top in oracle_limits(a[0]):
                yield (label + ", with an oracle's limit", "intmax", (a[0], top, a[1]))


def requests(seed, count):
    yield from APPENDIX_C
    yield from integer_sets()
    yield from huffman_sets()
    yield from string_sets()
    yield from more_string_sets()
    yield from static_sets()
    yield from long_sets()
    rng = random.Random(seed)
    for _ in range(count):
        s = random_string(rng)
        yield ("random string", "huffenc", (s,))
        yield ("random string", "huffdec", (huffman_encode(s),))
        yield from huffman_mutations(rng, s)
        for h in (0, 1):
            yield ("random string", "strenc", (h, s))
            yield from string_cases("random string literal", h, s, rng)
    for _ in range(count // 2):
        n, data = random_int_data(rng)
        yield from with_limits("random octets", n, data, rng.choice([None, rng.randrange(2 ** 40)]))
        yield ("random octets", "encint", (n, rng.randrange(2 ** (8 - n)),
                                            rng.choice([rng.randrange(300),
                                                        rng.randrange(2 ** 40),
                                                        rng.randrange(2 ** 80)])))


# Request lines, each sent with LF after it, that the tool must answer
# `error`. One ending in CR is sent ending in CR LF.
MALFORMED = ["", " ", "\r", "int", "int 5", "int 5 0a 0a", "INT 5 0a", "Int 5 0a", "int 5 0A",
             "int 5 0", "int 5 0a0", "int 5 0g", "int 5 0g\r", "int 5 --", "int 5 -0a",
             "int 0 0a", "int 9 0a", "int 10 0a", "int -1 0a", "int +5 0a", "int 5.0 0a",
             "int  5 0a", "int 5 0a ", "int 5 0a \r", " int 5 0a", "int\t5\t0a", "int 5 0a\t",
             "int 5 ", "int 5 0a\r\r", "int 5\r 0a",
             "intmax 5 0a", "intmax 5 -1 0a", "intmax 5 1e3 0a", "intmax 5 - 0a",
             "intmax 5 +3 0a", "intmax 5 3 0a ff", "encint 5 8 1", "encint 8 1 0",
             "encint 1 128 0", "encint 7 2 0", "encint 5 0", "encint 5 0 -1", "encint 5 0 0x1f",
             "encint 0 0 1", "encint 9 0 1", "encint 5 0 1 1", "huffdec", "huffdec 1f 1f",
             "huffdec 1F", "huffdec \u00e9", "huffdec 1", "huffenc 6", "huffenc", "strdec",
             "strdec 0", "strdec 00 00", "strenc 2 61", "strenc - 61", "strenc 1", "strenc 01 61",
             "strenc 1 6", "static", "static -1", "static 1 2", "static ", "static x",
             "static 0x10", "static \u0661", "static 1\r\r", "nop", "INT", "huffenc --",
             "strdec -\x00", "int 5 0a\x00", "huffdec 1f\x0b",
             "intmax 0 1000 0a", "intmax 9 1000 0a", "intmax x 1000 0a", "intmax 05x 1000 0a",
             "intmax 5 1000 0A", "intmax 5 1000 0g", "intmax 5 1000 0", "intmax 5 1000",
             "encint 5 x 1", "encint 5 1e1 1", "encint 5 -0 1", "huffenc 6A", "huffdec 6A",
             "strdec 0A", "strenc 1 6A", "strenc 0 6A", "strenc 0 6"]

# Well-formed but odd: leading zeros, numbers past 64 bits, `-`, CR LF.
ODD = ["int 05 0a", "int 008 ff", "static 007", "static 0", "static 18446744073709551617",
       "encint 008 0 1", "encint 1 000127 0", "intmax 5 00 00", "intmax 1 0 -",
       "intmax 8 340282366920938463463374607431768211456 ff8080808080808080808080808001",
       "encint 8 0 340282366920938463463374607431768211456", "huffdec -", "huffenc -",
       "strenc 1 -", "strenc 0 -", "strdec -", "int 1 -", "int 8 ffffffffffffffffffffff7f",
       "static 1\r", "int 5 0a\r"]

# Last lines sent alone, as they are sent, and the answer due: with no
# LF, with CR LF, and with a lone CR, which is not a line ending.
AT_EOF = [("int 5 0a", "OK 10 -"), ("int 5 0a\r\n", "OK 10 -"),
          ("static 2\r\n", "OK 3a6d6574686f64 474554"), ("int 5 0a\r", "error")]


def cli_cases():
    """Runs of the command-line modes: (arguments, what the run must
    print on standard output, without the last LF, and its exit status),
    from the model. A run that does not decode, malformed HEX and wrong
    arguments print nothing on standard output, and exit with 1, 2 and
    2."""
    cases = []
    for text in ["", "a", "www.example.com", "no-cache", "custom-value",
                 "Mon, 21 Oct 2013 20:13:22 GMT", "\u00e9\u20ac", " ~\x7f"]:
        cases.append((["huffman-encode", text], hx(huffman_encode(text.encode("utf-8"))), 0))
    for d in [b"", huffman_encode(b"a"), huffman_encode(bytes(range(256))), b"\x00", b"\xff",
              b"\xff\xff\xff\xff", b"\x1f\xff", octets_of(HUFFMAN[256] + "11")]:
        out, _ = huffman_decode(d)
        cases.append((["huffman-decode", hx(d)], hx(out) if out is not None else "",
                      0 if out is not None else 1))
    for lit in [encode_string(0, b"abc") + b"\x01", encode_string(1, b"custom-key"), b"\x05ab",
                b"\x7f\x80\x00", b"\x81\x00", b"", b"\x00"]:
        r, _ = decode_string(lit)
        cases.append((["string-decode", hx(lit)], f"{hx(r[0])} {hx(r[1])}" if r else "",
                      0 if r else 1))
    for bad in ["", "1F", "1", "zz", "0x1f", "1f 1f", "-1"]:
        cases.append((["huffman-decode", bad], "", 2))
        cases.append((["string-decode", bad], "", 2))
    for args in [[], ["bogus"], ["huffman-decode"], ["huffman-encode", "a", "b"],
                 ["serve", "x"], ["string-decode", "00", "00"]]:
        cases.append((args, "", 2))
    return cases


def run_cli(cases):
    """How many runs print and exit as `cli_cases` says, and a failure
    for each other."""
    right, failures = 0, []
    for args, out, status in cases:
        try:
            p = subprocess.run([str(EXE)] + args, capture_output=True, timeout=60)
            got, code_ = p.stdout.decode("utf-8", "backslashreplace"), p.returncode
            if got.endswith("\n"):
                got = got[:-1]
        except (OSError, subprocess.SubprocessError) as e:
            got, code_ = str(e), None
        if (got, code_) == (out, status):
            right += 1
        else:
            failures.append((f"hpack {' '.join(repr(a) for a in args)}",
                             f"{out!r}, exit {status}", f"{short(got, 160)!r}, exit {code_}"))
    return right, failures

# ---------------------------------------------------------------------


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def short(text, n=200):
    return text if len(text) <= n else text[:n] + f"... ({len(text)} characters)"


APPENDIX_C = []


def main():
    global HUFFMAN, STATIC, EXAMPLES, APPENDIX_C
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261027)
    ap.add_argument("--count", type=count_arg, default=8000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    args = ap.parse_args()
    os.environ["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    try:
        HUFFMAN, STATIC, EXAMPLES = read_rfc()
    except (OSError, RFCError, StopIteration) as e:
        give_up(f"the model could not read {RFC.name}: {e}")
    SYMBOL_OF.update({c: s for s, c in enumerate(HUFFMAN)})
    try:
        APPENDIX_C, ints_right, blocks_right = appendix_c()
    except (RFCError, IndexError) as e:
        give_up(f"the model could not read Appendix C: {e}")
    APPENDIX_C = [("Appendix C", op, a) for op, a in APPENDIX_C]

    try:
        build = subprocess.run(["lake", "build", "hpack"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        if build.returncode != 0:
            print(build.stdout + build.stderr)
            give_up("`lake build hpack` failed")
    except (OSError, subprocess.SubprocessError) as e:
        give_up(f"`lake build hpack` failed: {e}")

    failures = []
    if ints_right != len(C1):
        failures.append(("the model on Appendix C.1", f"{len(C1)} of {len(C1)}",
                         f"{ints_right} of {len(C1)}"))
    if blocks_right != len(EXAMPLES):
        failures.append(("the model on Appendix C.2 to C.6", f"{len(EXAMPLES)} of {len(EXAMPLES)}",
                         f"{blocks_right} of {len(EXAMPLES)}"))

    cli = cli_cases()
    cli_right, cli_failures = run_cli(cli)
    failures += cli_failures

    oracles, left_out = [], []
    for name, setup in ORACLE_SETUPS:
        if args.no_oracles:
            left_out.append((name, "--no-oracles"))
            continue
        try:
            oracles.append(setup())
        except Exception as e:  # any oracle that cannot start is left out, and recorded
            left_out.append((name, str(e).splitlines()[0][:300] if str(e) else type(e).__name__))
    for name, why in left_out:
        print(f"oracle left out: {name}: {why}")

    items = list(inputs(args.seed, args.count))
    requests = [request(op, a) for _, op, a in items]
    lines = [r + ("\r\n" if i % 7 == 6 else "\n") for i, r in enumerate(requests)]
    odd = MALFORMED + ODD
    out, problems = run_parallel([str(EXE), "serve"], lines + [m + "\n" for m in odd], JOBS)
    for problem in problems:
        failures.append(("(whole run)", "a clean run", problem))
    tool, odd_out = out[:len(items)], out[len(items):]
    malformed_right = sum(1 for m, a in zip(MALFORMED, odd_out) if a == "error")
    for m in MALFORMED:
        if model_line(m + "\n") != "error":
            failures.append((f"the model on {m!r}", "error", model_line(m + "\n")))
    odd_right = 0
    for m, a in zip(odd, odd_out):
        want = model_line(m + "\n")
        if a == want:
            odd_right += m in ODD
        else:
            failures.append((f"request {m!r}", want, a))
    eof_right = 0
    for req, want in AT_EOF:
        if model_line(req) != want:
            failures.append((f"the model on {req!r} at end of input", want, model_line(req)))
        got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    # Against the model.
    wants, whys, answers = [], [], []
    differ_model = 0
    refused = {}
    for (label, op, a), got in zip(items, tool):
        answer, why = model(op, a)
        want = render(op, answer)
        answers.append(answer)
        wants.append(want)
        whys.append(why)
        if why is not None:
            kind = {"int": "integer", "intmax": "integer"}.get(op, op)
            refused[(kind, why)] = refused.get((kind, why), 0) + 1
        if got != want:
            differ_model += 1
            failures.append((short(request(op, a)), short(want, 160), short(got, 160)))

    # Against the oracles.
    oracle_out = {}

    def ask(o):
        try:
            oracle_out[o.name] = o.answers(lines)
        except (RuntimeError, OSError) as e:
            oracle_out[o.name] = e

    threads = [threading.Thread(target=ask, args=(o,)) for o in oracles]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    for o in list(oracles):
        if isinstance(oracle_out[o.name], Exception):
            failures.append((f"({o.name} oracle run)", "a clean run", str(oracle_out[o.name])[:300]))
            oracles.remove(o)
    names = [o.name for o in oracles]
    asked = {o: 0 for o in names}
    agree = {o: 0 for o in names}
    by_op = {o: {} for o in names}
    named = {o: {} for o in names}
    limited = {o: 0 for o in names}
    for i, (label, op, a) in enumerate(items):
        got = tool[i]
        for o in names:
            theirs = oracle_out[o][i]
            if theirs == "n/a":
                continue
            if theirs == "FAIL" and got != "FAIL" and beyond_limit(o, op, answers[i]):
                limited[o] += 1
                continue
            asked[o] += 1
            by_op[o][op] = by_op[o].get(op, 0) + 1
            if theirs == got:
                agree[o] += 1
                continue
            reason = difference_reason(o, op, a, whys[i], got, theirs)
            if reason is None:
                failures.append((f"{o}: {short(request(op, a))}", short(got, 160),
                                 short(theirs, 160)))
            else:
                n, example = named[o].get(reason, (0, None))
                named[o][reason] = (n + 1, example or request(op, a))

    by_label = {}
    for label, op, _ in items:
        key = f"{label} {op}"
        by_label[key] = by_label.get(key, 0) + 1

    def read_count(ops):
        picked = [(w, y) for (_, op, _), w, y in zip(items, wants, whys) if op in ops]
        return len(picked), sum(1 for w, y in picked if y is None)

    def refusals(kind):
        return ", ".join(f"{why} {n}" for (k, why), n in
                         sorted(refused.items(), key=lambda kv: -kv[1]) if k == kind)

    n_int, ok_int = read_count({"int", "intmax"})
    n_huff, ok_huff = read_count({"huffdec"})
    n_str, ok_str = read_count({"strdec"})
    n_static, ok_static = read_count({"static"})
    encodes = {op: sum(1 for _, o, _ in items if o == op) for op in ("encint", "huffenc", "strenc")}
    nonminimal = sum(1 for y in whys if y is not None and NONMINIMAL in y)

    lines_out = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        "- Oracle: the model of RFC 7541 in `tests/run_tests.py`, with the Huffman code of "
        "Appendix B and the static table of Appendix A read from `tests/rfc7541.txt`"
        + "".join(f"; {o.name} {o.version}" for o in oracles),
    ]
    lines_out += [f"- {o.name}: {o.version}" for o in oracles]
    lines_out += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out)
                                  if left_out else "none"),
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Answers that differ from the model: {differ_model}",
        f"- RFC 7541: `tests/rfc7541.txt`, SHA-256 {RFC_SHA256}; Appendix B: 257 codes, the bits, "
        f"hex and length columns agree, and the code is prefix-free and complete; Appendix A: "
        f"{len(STATIC)} entries",
        f"- Appendix C read by the model as the RFC reads it: the integers of C.1, {ints_right} of "
        f"{len(C1)}; the header blocks of C.2 to C.6, {blocks_right} of {len(EXAMPLES)}, each "
        f"decoded to its header list and written again octet for octet",
        f"- Integers read (`int` and `intmax`): {n_int}, of which {ok_int} give a value; why the "
        f"model refuses the others: {refusals('integer')}",
        f"- Huffman strings read: {n_huff}, of which {ok_huff} decode; why the model refuses the "
        f"others: {refusals('huffdec')}",
        f"- String literals read: {n_str}, of which {ok_str} decode; why the model refuses the "
        f"others: {refusals('strdec')}",
        f"- Static indices asked: {n_static}, of which {ok_static} are in the table",
        f"- Encodings asked for: integers {encodes['encint']}, Huffman {encodes['huffenc']}, "
        f"string literals {encodes['strenc']}",
        f"- Inputs the code refuses for an integer written in more octets than it needs: "
        f"{nonminimal}",
        "- Agreement with each oracle over the requests it answers: "
        + ", ".join(f"{o} {agree[o]} of {asked[o]}" for o in names),
        "- Refusals not compared because the request passes the oracle's own limit (nghttp2: a "
        "header field of more than 65,536 octets): "
        + ", ".join(f"{o} {limited[o]}" for o in names),
        "- Requests each oracle answers, by operation: "
        + "; ".join(f"{o}: " + ", ".join(f"{op} {n}" for op, n in sorted(by_op[o].items()))
                    for o in names),
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}; odd but "
        f"well-formed requests answered as the model says: {odd_right} of {len(ODD)}",
        f"- Requests ending in CR LF: every seventh, {len(requests) // 7}",
        f"- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: "
        f"{eof_right} of {len(AT_EOF)}",
        f"- Command-line modes (`huffman-encode`, `huffman-decode`, `string-decode`, and wrong "
        f"arguments), printing and exiting as the model says: {cli_right} of {len(cli)}",
        f"- Failures: {len(failures)}",
        "",
        "## Where the oracles differ",
        "",
        "Each disagreement is counted under the reason the model confirms, with the first "
        "input that showed it. The tool refuses each of these, and the oracle answers.",
        "",
    ]
    for o in names:
        lines_out.append(f"### {o}")
        lines_out.append("")
        if not named[o]:
            lines_out.append("No disagreement.")
        for reason, (n, example) in sorted(named[o].items(), key=lambda kv: -kv[1][0]):
            lines_out.append(f"- {reason}: {n}; for example {code(short(example, 240))}")
        lines_out.append("")
    if failures:
        lines_out += ["## Failures", ""]
        lines_out += [f"- {code(req)}: expected {code(want)}, got {code(got)}"
                      for req, want, got in failures[:50]]
        lines_out.append("")
    write(lines_out)
    print(f"{len(items)} inputs, {len(oracles)} oracles, {len(failures)} failures; results in "
          f"{RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
