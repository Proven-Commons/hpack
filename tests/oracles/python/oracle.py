"""The Python oracle for tests/run_tests.py: the `hpack` package, at the
version requirements.txt pins with its hash, installed by run_tests.py
into a virtual environment under .lake/oracle-python.

Each line of standard input is one request in the form `hpack serve`
reads (octets in lower-case hex, `-` for none; numbers in decimal), and
each answer is in the form it writes, `OK ...` or `FAIL`. A request the
package cannot answer is answered `n/a`, and a line this program cannot
read `error`.

    intmax N MAX HEX    hpack.hpack.decode_integer, and FAIL when the
                        value is above MAX. Only for MAX up to
                        2^N - 2 + 2^35: decode_integer reads at most
                        five octets after the prefix, which hold every
                        value up to there written in the fewest octets.
    encint N HIGH V     hpack.hpack.encode_integer, with HIGH put in the
                        bits of the first octet above the prefix, as
                        the Encoder sets the H flag and the
                        representation bits.
    huffdec HEX         hpack.huffman_table.decode_huffman
    huffenc HEX         hpack.huffman.HuffmanEncoder, with the code of
                        hpack.huffman_constants
    strdec HEX          a fresh hpack.Decoder reads, with raw=True, the
                        header block 00 01 61 and the string literal: a
                        literal header field without indexing, with the
                        name "a" and the literal as its value. Where the
                        literal ends is read from its length with
                        decode_integer; the octets after it are the
                        rest.
    strenc H HEX        a fresh hpack.Encoder encodes the header field
                        ("a", the octets) as never indexed, with
                        huffman=H; the answer is what it writes after
                        the representation octet and the name "a".
    static I            a fresh hpack.Decoder reads the indexed header
                        field I.

`int` is `n/a`: decode_integer has a limit, so it is asked only
through `intmax`.
"""

import sys

import hpack
from hpack.hpack import decode_integer, encode_integer
from hpack.huffman import HuffmanEncoder
from hpack.huffman_constants import REQUEST_CODES, REQUEST_CODES_LENGTH
from hpack.huffman_table import decode_huffman

ENCODER = HuffmanEncoder(REQUEST_CODES, REQUEST_CODES_LENGTH)


class Malformed(Exception):
    pass


def octets(f):
    if f == "-":
        return b""
    if not f or f != f.lower():
        raise Malformed
    try:
        return bytes.fromhex(f)
    except ValueError:
        raise Malformed from None


def number(f):
    if not f or not all("0" <= c <= "9" for c in f):
        raise Malformed
    return int(f)


def hexf(b):
    return bytes(b).hex() or "-"


def answer(line):
    parts = line.split(" ")
    op, args = parts[0], parts[1:]
    try:
        if op == "intmax" and len(args) == 3:
            n, top, data = number(args[0]), number(args[1]), octets(args[2])
            if not 1 <= n <= 8:
                raise Malformed
            if top > 2 ** n - 2 + 2 ** 35:
                return "n/a"
            try:
                value, used = decode_integer(data, n)
            except hpack.HPACKDecodingError:
                return "FAIL"
            return "FAIL" if value > top else f"OK {value} {hexf(data[used:])}"
        if op == "encint" and len(args) == 3:
            n, high, value = number(args[0]), number(args[1]), number(args[2])
            if not 1 <= n <= 8 or high >= 2 ** (8 - n):
                raise Malformed
            out = encode_integer(value, n)
            out[0] |= high << n
            return f"OK {hexf(out)}"
        if op == "huffdec" and len(args) == 1:
            d = octets(args[0])
            try:
                return f"OK {hexf(decode_huffman(d))}"
            except hpack.HPACKDecodingError:
                return "FAIL"
        if op == "huffenc" and len(args) == 1:
            return f"OK {hexf(ENCODER.encode(octets(args[0])))}"
        if op == "strdec" and len(args) == 1:
            data = octets(args[0])
            try:
                length, used = decode_integer(data, 7)
                end = used + length
                headers = hpack.Decoder().decode(b"\x00\x01a" + data[:end], raw=True)
            except hpack.HPACKError:
                return "FAIL"
            if len(headers) != 1 or headers[0][0] != b"a":
                return f"unreadable {headers!r}"
            return f"OK {hexf(headers[0][1])} {hexf(data[end:])}"
        if op == "strenc" and len(args) == 2:
            if args[0] not in ("0", "1"):
                raise Malformed
            huffman = args[0] == "1"
            out = hpack.Encoder().encode([(b"a", octets(args[1]), True)], huffman=huffman)
            # 10 (never indexed, new name), then "a": 81 1f with
            # Huffman coding, 01 61 without.
            head = b"\x10\x81\x1f" if huffman else b"\x10\x01a"
            if out[:3] != head:
                return f"unreadable {out.hex()}"
            return f"OK {hexf(out[3:])}"
        if op == "static" and len(args) == 1:
            index = number(args[0])
            block = encode_integer(index, 7)
            block[0] |= 0x80
            try:
                headers = hpack.Decoder().decode(bytes(block), raw=True)
            except hpack.HPACKError:
                return "FAIL"
            if len(headers) != 1:
                return f"unreadable {headers!r}"
            return f"OK {hexf(headers[0][0])} {hexf(headers[0][1])}"
        if op == "int" and len(args) == 2:
            return "n/a"
    except Malformed:
        return "error"
    return "error"


def main():
    out = []
    for raw in sys.stdin.buffer:
        line = raw.decode("utf-8", "replace").rstrip("\r\n")
        try:
            out.append(answer(line))
        except Exception as e:  # an exception is an answer to report, not a crash
            out.append(f"unreadable {type(e).__name__}: {e}".replace("\n", " "))
    sys.stdout.write("".join(a + "\n" for a in out))


if __name__ == "__main__":
    main()
