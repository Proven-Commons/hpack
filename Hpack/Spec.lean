/-
  The statements this library is proved to meet, for a reviewer to
  approve. Each `sorry` is proved in `Hpack/Proofs/` under the same name, and
  `lake comparator` checks that each proof proves exactly the statement
  here.

  The definitions they use are in `Hpack/Spec/Defs.lean`, written from
  RFC 7541. The functions they are about are in `Hpack/Basic.lean`.
-/

import Hpack.Spec.Defs
import Hpack

namespace Hpack.Spec

/-! ## Integers (section 5.1) -/

/-- The encoder writes what the encoding pseudocode of section 5.1
    writes, for every prefix size from 1 to 8 and every value, with any
    bits above the prefix. -/
theorem encodeInt_eq (n high i : Nat) (hn : 1 ≤ n ∧ n ≤ 8) (hhigh : high < 2 ^ (8 - n)) :
    Hpack.encodeInt n high i = intEncode n high i := sorry

/-- The decoder accepts exactly what the encoding pseudocode writes,
    whatever the bits above the prefix are, and gives back the value and
    the octets after it. So it never reads past the end of the input, and
    each value has exactly one encoding it accepts for each choice of
    the bits above the prefix. -/
theorem decodeInt_iff (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    Hpack.decodeInt n b = some (i, rest) ↔
      ∃ high, high < 2 ^ (8 - n) ∧ b = intEncode n high i ++ rest := sorry

/-- What the decoder accepts, the decoding pseudocode of section 5.1
    reads the same way. -/
theorem decodeInt_rfc (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    Hpack.decodeInt n b = some (i, rest) → intDecode n b = some (i, rest) := sorry

/-- What the decoding pseudocode reads, the decoder reads the same way,
    except an encoding whose last octet is 0 and follows at least one
    octet with the continuation bit set: an encoding longer than it need
    be. RFC 7541 does not require minimal encodings, and other decoders
    read these; this one refuses them, so that each value has one
    encoding. That choice is stricter than the RFC. -/
theorem decodeInt_of_rfc (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    intDecode n b = some (i, rest) →
      Hpack.decodeInt n b = some (i, rest) ∨
      ∃ pre c, pre ≠ [] ∧ 128 ≤ c.toNat ∧ b = pre ++ [c, 0] ++ rest := sorry

/-- With a stated limit, the decoder accepts exactly the encodings of
    values up to the limit, and fails on every value above it. -/
theorem decodeIntUpTo_iff (n max : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    Hpack.decodeIntUpTo n max b = some (i, rest) ↔
      i ≤ max ∧ ∃ high, high < 2 ^ (8 - n) ∧ b = intEncode n high i ++ rest := sorry

/-- A prefix size outside 1 to 8, which section 5.1 does not allow
    ("The prefix size, N, is always between 1 and 8 bits"), is refused,
    with or without a limit. -/
theorem decodeInt_prefix (n max : Nat) (b : List UInt8) (hn : n = 0 ∨ 8 < n) :
    Hpack.decodeInt n b = none ∧ Hpack.decodeIntUpTo n max b = none := sorry

/-! ## The Huffman code (section 5.2, Appendix B) -/

/-- The encoder writes the codes of Appendix B and pads with ones. -/
theorem huffmanEncode_spec (s : List UInt8) :
    HuffmanEncodes s (Hpack.huffmanEncode s) := sorry

/-- The decoder accepts exactly the Huffman encodings, and gives back
    what was encoded. It rejects EOS, padding longer than 7 bits, and
    padding with a zero bit, as section 5.2 requires. -/
theorem huffmanDecode_iff (d s : List UInt8) :
    Hpack.huffmanDecode d = some s ↔ HuffmanEncodes s d := sorry

/-- Decoding an encoding gives back the octets. -/
theorem huffmanDecode_encode (s : List UInt8) :
    Hpack.huffmanDecode (Hpack.huffmanEncode s) = some s := sorry

/-- What the decoder accepts is exactly what the encoder writes for the
    decoded octets: each string has one Huffman encoding. -/
theorem huffmanEncode_decode (d s : List UInt8) :
    Hpack.huffmanDecode d = some s → Hpack.huffmanEncode s = d := sorry

/-! ## String literals (section 5.2) -/

/-- The encoder writes a string literal for `s`, with the H flag set
    exactly when `huffman` is true. -/
theorem encodeString_spec (huffman : Bool) (s : List UInt8) :
    StringLiteral huffman s (Hpack.encodeString huffman s) := sorry

/-- The decoder accepts exactly a string literal followed by anything,
    and gives back its octets and what follows. So it never reads past
    the end of the input. `StringLiteral` writes the length in the fewest
    octets, so a length written in more is refused. -/
theorem decodeString_iff (b s rest : List UInt8) :
    Hpack.decodeString b = some (s, rest) ↔
      ∃ huffman lit, StringLiteral huffman s lit ∧ b = lit ++ rest := sorry

/-- Decoding an encoding gives back the octets and what follows. -/
theorem decodeString_encode (huffman : Bool) (s rest : List UInt8) :
    Hpack.decodeString (Hpack.encodeString huffman s ++ rest) = some (s, rest) := sorry

/-! ## The static table (Appendix A) -/

/-- Index `i` names entry `i` of Table 1, counting from 1, and no other
    index names an entry. -/
theorem staticEntry_eq (i : Nat) :
    Hpack.staticEntry i = if i = 0 then none else staticTable[i - 1]? := sorry

/-! ## The examples of Appendix C, and what section 5.2 rejects -/

/-- Appendix C.1: 10 and 1337 with a 5-bit prefix, and 42 at an octet
    boundary. -/
theorem rfc_integers :
    Hpack.encodeInt 5 0 10 = [0x0a] ∧
    Hpack.encodeInt 5 0 1337 = [0x1f, 0x9a, 0x0a] ∧
    Hpack.encodeInt 8 0 42 = [0x2a] ∧
    Hpack.decodeInt 5 [0x0a] = some (10, []) ∧
    Hpack.decodeInt 5 [0x1f, 0x9a, 0x0a] = some (1337, []) ∧
    Hpack.decodeInt 8 [0x2a] = some (42, []) := sorry

/-- The twelve Huffman encoded strings of Appendix C.4 and C.6. -/
theorem rfc_huffman :
    Hpack.huffmanEncode (ascii "www.example.com") =
      [0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff] ∧
    Hpack.huffmanEncode (ascii "no-cache") = [0xa8, 0xeb, 0x10, 0x64, 0x9c, 0xbf] ∧
    Hpack.huffmanEncode (ascii "custom-key") =
      [0x25, 0xa8, 0x49, 0xe9, 0x5b, 0xa9, 0x7d, 0x7f] ∧
    Hpack.huffmanEncode (ascii "custom-value") =
      [0x25, 0xa8, 0x49, 0xe9, 0x5b, 0xb8, 0xe8, 0xb4, 0xbf] ∧
    Hpack.huffmanEncode (ascii "302") = [0x64, 0x02] ∧
    Hpack.huffmanEncode (ascii "private") = [0xae, 0xc3, 0x77, 0x1a, 0x4b] ∧
    Hpack.huffmanEncode (ascii "Mon, 21 Oct 2013 20:13:21 GMT") =
      [0xd0, 0x7a, 0xbe, 0x94, 0x10, 0x54, 0xd4, 0x44, 0xa8, 0x20, 0x05, 0x95,
       0x04, 0x0b, 0x81, 0x66, 0xe0, 0x82, 0xa6, 0x2d, 0x1b, 0xff] ∧
    Hpack.huffmanEncode (ascii "Mon, 21 Oct 2013 20:13:22 GMT") =
      [0xd0, 0x7a, 0xbe, 0x94, 0x10, 0x54, 0xd4, 0x44, 0xa8, 0x20, 0x05, 0x95,
       0x04, 0x0b, 0x81, 0x66, 0xe0, 0x84, 0xa6, 0x2d, 0x1b, 0xff] ∧
    Hpack.huffmanEncode (ascii "https://www.example.com") =
      [0x9d, 0x29, 0xad, 0x17, 0x18, 0x63, 0xc7, 0x8f, 0x0b, 0x97, 0xc8, 0xe9,
       0xae, 0x82, 0xae, 0x43, 0xd3] ∧
    Hpack.huffmanEncode (ascii "307") = [0x64, 0x0e, 0xff] ∧
    Hpack.huffmanEncode (ascii "gzip") = [0x9b, 0xd9, 0xab] ∧
    Hpack.huffmanEncode (ascii "foo=ASDJKHQKBZXOQWEOPIUAXQWEOIU; max-age=3600; version=1") =
      [0x94, 0xe7, 0x82, 0x1d, 0xd7, 0xf2, 0xe6, 0xc7, 0xb3, 0x35, 0xdf, 0xdf,
       0xcd, 0x5b, 0x39, 0x60, 0xd5, 0xaf, 0x27, 0x08, 0x7f, 0x36, 0x72, 0xc1,
       0xab, 0x27, 0x0f, 0xb5, 0x29, 0x1f, 0x95, 0x87, 0x31, 0x60, 0x65, 0xc0,
       0x03, 0xed, 0x4e, 0xe5, 0xb1, 0x06, 0x3d, 0x50, 0x07] := sorry

/-- What section 5.2 tells a decoder to reject. `a` is `00011`, so 0x1f
    is `a` and three bits of padding. Followed by 0xff, the padding is 11
    bits; as 0x1e, the padding has a zero bit. Four octets of ones hold
    EOS, which is 30 ones. A lone 0xff is 8 bits of padding. -/
theorem huffman_rejects :
    Hpack.huffmanDecode [0x1f] = some (ascii "a") ∧
    Hpack.huffmanDecode [0x1f, 0xff] = none ∧
    Hpack.huffmanDecode [0x1e] = none ∧
    Hpack.huffmanDecode [0xff, 0xff, 0xff, 0xff] = none ∧
    Hpack.huffmanDecode [0xff] = none := sorry

end Hpack.Spec
