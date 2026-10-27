# hpack: the stateless part of HPACK (RFC 7541), proved

HPACK is how HTTP/2 compresses header fields, and QPACK (HTTP/3) uses the same integers and the same Huffman code. Every HTTP/2 client, server and proxy decodes it from bytes a peer chose. Mistakes here are a classic source of out-of-bounds reads and request smuggling: an integer read past the end of its input, a Huffman string with bad padding accepted by one parser and rejected by another, a length that runs past the data.

This library reads and writes the parts of HPACK that need no state, in Lean:

- integers with an N-bit prefix (section 5.1);
- string literals and the Huffman code (section 5.2 and Appendix B);
- the static table (Appendix A).

Machine-checked proofs show:

- The integer decoder accepts exactly what the RFC's encoding pseudocode writes, never reads past the end of its input, and reads each value the way the RFC's decoding pseudocode does. It refuses only encodings longer than they need be. The RFC does not require that refusal, and other decoders read such encodings; this library refuses them so that each value has one encoding, a choice stricter than the RFC. It also refuses a prefix size outside 1 to 8, and, with a stated limit, every value above the limit.
- The Huffman decoder accepts exactly the Huffman encodings and gives back what was encoded. It rejects EOS, padding longer than 7 bits, and padding that is not all ones, as section 5.2 requires. Each string has exactly one encoding it accepts.
- The string literal decoder accepts exactly a string literal whose length is written in the fewest octets, followed by anything. It never reads past the end of its input, and gives back the string.
- The encoders write what the RFC says, and decoding what they write gives it back.
- The static table is Table 1 of Appendix A. The integer examples of Appendix C.1 and all twelve Huffman strings of C.4 and C.6 come out byte for byte. The header blocks of Appendix C need the second slice.

It is tested against a model of the RFC and three other implementations: Python `hpack` 4.2.0, Go's `golang.org/x/net/http2/hpack` (x/net v0.50.0), and nghttp2 1.59.0. The record is in `tests/TEST-RESULTS.md`. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean, on `List UInt8`:

- `Hpack.encodeInt (n high i : Nat) : List UInt8` and `Hpack.decodeInt (n : Nat) : List UInt8 → Option (Nat × List UInt8)`, for a prefix of `n` bits, 1 to 8. `high` holds the bits of the first octet above the prefix. `decodeInt` refuses any other `n`; what `encodeInt` writes for one is not specified. `Hpack.decodeIntUpTo n max` refuses values above `max`.
- `Hpack.huffmanEncode : List UInt8 → List UInt8` and `Hpack.huffmanDecode : List UInt8 → Option (List UInt8)`.
- `Hpack.encodeString (huffman : Bool) : List UInt8 → List UInt8` and `Hpack.decodeString : List UInt8 → Option (List UInt8 × List UInt8)`. The decoder gives the string and the octets after it.
- `Hpack.staticEntry : Nat → Option (String × String)`, the name and value at an index from 1 to 61.

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The integer encoder writes what the encoding pseudocode of section 5.1 writes, for every prefix size from 1 to 8, every value, and any bits above the prefix. | `Spec.encodeInt_eq` |
| The integer decoder accepts exactly those encodings, followed by anything, and gives back the value and what follows. | `Spec.decodeInt_iff` |
| What it accepts, the decoding pseudocode of section 5.1 reads the same way. | `Spec.decodeInt_rfc` |
| What the decoding pseudocode reads, it reads the same way, except an encoding whose last octet is 0 after another continuation octet. | `Spec.decodeInt_of_rfc` |
| With a limit, it accepts exactly the encodings of values up to the limit. | `Spec.decodeIntUpTo_iff` |
| A prefix size outside 1 to 8 is refused, with or without a limit. | `Spec.decodeInt_prefix` |
| The Huffman encoder writes the codes of Appendix B and pads with ones. `Spec.HuffmanEncodes` states section 5.2. | `Spec.huffmanEncode_spec` |
| The Huffman decoder accepts exactly the Huffman encodings and gives back what was encoded. | `Spec.huffmanDecode_iff` |
| Decoding a Huffman encoding gives back the string, and what the decoder accepts is exactly what the encoder writes for the result. | `Spec.huffmanDecode_encode`, `Spec.huffmanEncode_decode` |
| The string encoder writes a string literal, with the H flag as asked. `Spec.StringLiteral` states section 5.2. | `Spec.encodeString_spec` |
| The string decoder accepts exactly a string literal, its length in the fewest octets, followed by anything, and gives back the string and what follows. | `Spec.decodeString_iff`, `Spec.decodeString_encode` |
| Index `i` gives entry `i` of Table 1, and no other index gives an entry. | `Spec.staticEntry_eq` |
| The integer examples of Appendix C.1, all twelve Huffman strings of Appendix C.4 and C.6, and the three rejections of section 5.2 on examples. | `Spec.rfc_integers`, `Spec.rfc_huffman`, `Spec.huffman_rejects` |

A few facts about the 257 codes are checked by the kernel by evaluation:

- the code's table, taken from the "code as hex" column of Appendix B, equals the specification's, taken from the "code as bits" column;
- each code fits in its length;
- for two different symbols, the longer code never starts with the shorter one;
- EOS is 30 ones.

From these the proofs derive that no code is a prefix of another and that no code is all ones and shorter than 8 bits. The rest is proved for every input.

## What is not proved

- **The dynamic table and header blocks.** Section 6's representations, the dynamic table, its size updates and eviction, and the decoding of a whole header block are the second slice.
- **Time and memory.** No proof bounds them. The decoders are written to take time linear in their input: the integer decoder adds up a long encoding by halves rather than one octet at a time, the string decoder never measures more of the input than the string's length, and the Huffman decoder compares the bits it has read only with the codes of the same length, and refuses 30 bits that match no code, since no code is longer. The tests include long inputs of each kind.
- **The limits of section 7.4.** RFC 7541 says an implementation "has to set a limit for the values it accepts for integers, as well as for the encoded length", and for the length of string literals. `decodeInt` sets none: values and encodings have no upper bound, only the input's length. `decodeIntUpTo` sets a limit on the value, and the octets an accepted encoding takes then follow from it. `decodeString` sets no limit of its own: a string literal can be no longer than the input. Setting limits is left to the caller, and to the second slice.
- **Reading requests and printing answers in `Main.lean`.** The differential tests cover them: every request of `hpack serve`, and each command-line mode on valid, invalid and malformed input.

## Where other implementations differ

The tests compare each answer with every implementation that answers that kind of request, and count each disagreement under its reason, confirmed against the model. The record gives the counts for each implementation. There is one reason, and in every case this library refuses and the other answers:

- **Integers written in more octets than they need.** An integer whose last octet is 0 and follows at least one octet with the continuation bit set, such as `1f 80 00` for 31 with a 5-bit prefix, is read by all three. Python `hpack` and nghttp2 read up to five continuation octets, and Go up to nine. RFC 7541 does not require minimal encodings. This library refuses every such encoding anyway, so that each value has one encoding it accepts. In HTTP/2, such a refusal is a connection error, on input the others accept. The record counts the inputs this library refuses for this reason, among them string lengths written that way.

The others also limit the values they read. Python `hpack` reads at most five continuation octets, nghttp2 reads every integer as a 32-bit number, and Go refuses a table size above 2^32 - 1. This library has no limit unless one is given with `decodeIntUpTo`. So the tests ask each oracle only for integers up to a limit it keeps, 2^N - 2 + 2^35 for Python `hpack` and 2^32 - 1 for Go and nghttp2, and give the tool the same limit. nghttp2 also refuses a header field longer than 65,536 octets; the tests do not count its refusals of the long strings past that, and the record says how many there were. The Python oracle raises its decoder's own limit on a header list, 65,536 octets by default, so that it reads them.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number arithmetic, `UInt8`, and the conversion between strings and their characters.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and the implementations it compares against. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), Python 3 and a C compiler. The oracles also need pip (for Python `hpack`, pinned by hash), Go, and libnghttp2's headers (`apt install libnghttp2-dev`). The test script leaves out any it cannot build, and the record names them.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script builds the tool and the oracles. Its model reads the Huffman code and the static table from the copy of RFC 7541 in `tests/`, checked by SHA-256, and must decode every example of Appendix C as the RFC does. It then sends these inputs:

- the examples of Appendix C;
- integers for every prefix size, around every power of two up to 2^70, with every value of the bits above the prefix, cut short, and with extra zero octets, with and without a limit;
- every input of up to two octets to the Huffman decoder, every octet alone, random strings, and encodings with a bit flipped, EOS inserted, the padding extended, made of zeros or holding a zero, and the last octet cut;
- string literals, raw and Huffman, cut short, with the H flag flipped, with lengths written in more octets than they need, with Huffman data holding EOS, and with lengths far past the data;
- long inputs: integers of up to 1,001 continuation octets, and of 100,002 under a limit; string lengths written in 100,002 octets; strings of about 100 KB, one of every octet value and one of 30-bit codes;
- every static index from 0 to 100, and some far past the table;
- malformed requests, and CR LF line endings;
- each command-line mode, on input that decodes, input that does not, and malformed hex, and wrong arguments.

It then rewrites `tests/TEST-RESULTS.md`. `tests/plant_bugs.py` plants twenty bugs in a copy of the code and of `Main.lean`, one at a time, and records in `tests/PLANTED-BUGS.md` how many failures the tests report for each, against the model alone. Every bug must be caught.

## Layout

- `Hpack/Basic.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from RFC 7541.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests, the oracles, and the planted bugs.
