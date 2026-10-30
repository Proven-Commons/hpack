# Specification: hpack

HPACK (RFC 7541, https://www.rfc-editor.org/rfc/rfc7541) is the header compression format of HTTP/2. QPACK, the format of HTTP/3 (RFC 9204), uses the same integers and the same Huffman code. This library reads and writes the parts of HPACK that need no state:

- integers with an N-bit prefix (section 5.1);
- string literals and the Huffman code (section 5.2 and Appendix B);
- the static table (Appendix A).

The dynamic table, the header field representations of section 6, and the decoding of a whole header block are a later slice.

A reviewer who did not write this specification approves it. The approval also covers `Hpack/Spec.lean`, `Hpack/Spec/Defs.lean`, and the other files that `bar.toml` lists.

## Integers

An integer has a prefix of N bits, 1 to 8, at the end of its first octet. The other bits of that octet belong to whatever holds the integer: for a string length, the top bit is the H flag.

- **A value below 2^N - 1** fits in the prefix.
- **Any other value:** the prefix is all ones. The value minus 2^N - 1 follows in octets of seven bits each, least significant first, and every octet but the last has its top bit set.

`Hpack/Spec/Defs.lean` copies the RFC's encoding pseudocode (`intEncode`) and decoding pseudocode (`intDecode`) line for line.

**The encoder** writes what the encoding pseudocode writes.

**The decoder** accepts exactly what the encoding pseudocode writes, with any bits above the prefix, followed by anything, and gives back the value and what follows. It never reads past the end of its input. The decoding pseudocode reads one more kind of input, which this decoder refuses: an encoding longer than it need be, whose last octet is 0 and follows at least one octet with the continuation bit set. RFC 7541 does not require minimal encodings, and other decoders read these. Refusing them is a choice stricter than the RFC, made so that each value has exactly one encoding the decoder accepts, for each choice of the bits above the prefix. Values have no upper bound. A prefix size outside 1 to 8 is refused: section 5.1 says "The prefix size, N, is always between 1 and 8 bits". What the encoder writes for such a size is not specified.

**With a stated limit:** `decodeIntUpTo n max` also refuses every value above `max`.

## The Huffman code

Appendix B gives a code for each octet and for EOS (end of string). `Hpack/Spec/Defs.lean` copies its "code as bits" column as written.

**The encoding** of a string is the codes of its octets, one after another, then padding to the next octet boundary. Section 5.2 says the padding is "the most significant bits of the code corresponding to the EOS (end-of-string) symbol". That code is 30 ones and the padding is at most 7 bits, so the padding is up to 7 ones. `Hpack.Spec.HuffmanEncodes s d` states this.

**The decoder** accepts exactly the encodings. It rejects what section 5.2 says a decoder must reject:
- "A padding strictly longer than 7 bits";
- "A padding not corresponding to the most significant bits of the code for the EOS symbol";
- "A Huffman-encoded string literal containing the EOS symbol".

No code is a prefix of another, so each string has exactly one encoding. The decoder accepts that encoding and nothing else.

## String literals

A string literal is the H flag, the length of the string data as an integer with a 7-bit prefix, and the data. Here the length is written in the fewest octets, as the integer encoder writes it: the integer decoder refuses longer forms. With H = 0 the data is the string itself. With H = 1 it is the Huffman encoding of the string. `Hpack.Spec.StringLiteral` states this.

**The decoder** accepts exactly a string literal, its length in the fewest octets, followed by anything, and gives back the string and what follows. It never reads past the end of its input.

**The encoder** writes a string literal, Huffman encoded when asked.

## The static table

Index `i`, from 1 to 61, names entry `i` of Table 1 in Appendix A. No other index names an entry.

## What must always hold

Each property is a theorem in `Hpack/Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| The integer encoder writes what the pseudocode of section 5.1 writes. | `Hpack.Spec.encodeInt_eq` |
| The integer decoder accepts exactly those encodings, followed by anything. | `Hpack.Spec.decodeInt_iff` |
| What it accepts, the decoding pseudocode reads the same way. | `Hpack.Spec.decodeInt_rfc` |
| What the decoding pseudocode reads, it reads the same way, except encodings longer than they need be. | `Hpack.Spec.decodeInt_of_rfc` |
| A prefix size outside 1 to 8 is refused. | `Hpack.Spec.decodeInt_prefix` |
| With a limit, it accepts exactly the encodings of values up to the limit. | `Hpack.Spec.decodeIntUpTo_iff` |
| The Huffman encoder writes the codes and pads with ones. | `Hpack.Spec.huffmanEncode_spec` |
| The Huffman decoder accepts exactly the encodings and gives back what was encoded. | `Hpack.Spec.huffmanDecode_iff` |
| Decoding an encoding gives back the string. | `Hpack.Spec.huffmanDecode_encode` |
| What the decoder accepts is what the encoder writes for the result. | `Hpack.Spec.huffmanEncode_decode` |
| The string encoder writes a string literal, with H as asked. | `Hpack.Spec.encodeString_spec` |
| The string decoder accepts exactly a string literal, its length in the fewest octets, followed by anything. | `Hpack.Spec.decodeString_iff` |
| Decoding an encoding gives back the string and what follows. | `Hpack.Spec.decodeString_encode` |
| The static table is Table 1. | `Hpack.Spec.staticEntry_eq` |
| The integer examples of Appendix C.1. | `Hpack.Spec.rfc_integers` |
| All twelve Huffman strings of Appendix C.4 and C.6. | `Hpack.Spec.rfc_huffman` |
| The three rejections of section 5.2, on examples. | `Hpack.Spec.huffman_rejects` |

## The command-line tool

`Main.lean` has these modes:

- `hpack huffman-encode TEXT` prints the Huffman encoding of a text's UTF-8 octets, in hex.
- `hpack huffman-decode HEX` prints the octets a Huffman encoding decodes to, in hex, or exits with 1.
- `hpack string-decode HEX` prints the octets of the string literal at the start of some octets and the octets after it, in hex, or exits with 1.

HEX is lower-case hex digits in pairs, or `-` for no octets. Malformed HEX, or wrong arguments, exit with 2.
- `hpack serve` answers requests from the differential tests, one per line. The header comment of `Main.lean` gives the protocol.

Every answer comes from the functions above.
