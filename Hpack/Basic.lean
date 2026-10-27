/-
  HPACK (RFC 7541), the parts that need no state: integers with an
  N-bit prefix (section 5.1), string literals and the Huffman code
  (section 5.2, Appendix B), and the static table (Appendix A).
-/

namespace Hpack

/-! ## Integers (section 5.1) -/

/-- The octets after the prefix for a value `j`: seven bits each,
    least significant first, the top bit set on all but the last. -/
def encodeRest (j : Nat) : List UInt8 :=
  if j < 128 then [j.toUInt8] else (j % 128 + 128).toUInt8 :: encodeRest (j / 128)
termination_by j
decreasing_by omega

/-- `i` as an integer with an `n`-bit prefix (`1 ≤ n ≤ 8`). The bits of
    the first octet above the prefix hold `high`, for example the H flag
    of a string literal. -/
def encodeInt (n high i : Nat) : List UInt8 :=
  let top := high % 2 ^ (8 - n) * 2 ^ n
  if i < 2 ^ n - 1 then [(top + i).toUInt8]
  else (top + (2 ^ n - 1)).toUInt8 :: encodeRest (i - (2 ^ n - 1))

/-- The value of the octets after the prefix, and the octets after
    them. The last octet may be 0 only when it is the only one, so every
    value has one encoding. -/
def decodeRest : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else match decodeRest bs with
      | some (j, rest) => if j = 0 then none else some (b.toNat - 128 + 128 * j, rest)
      | none => none

/-- An integer with an `n`-bit prefix (`1 ≤ n ≤ 8`) at the start of the
    input, and the octets after it. The bits above the prefix are not
    read. Fails when the input ends first, and when the encoding is
    longer than it need be. -/
def decodeInt (n : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat % 2 ^ n < 2 ^ n - 1 then some (b.toNat % 2 ^ n, bs)
    else match decodeRest bs with
      | some (j, rest) => some (2 ^ n - 1 + j, rest)
      | none => none

/-- `decodeInt` with a stated limit: a value above `max` is an error,
    as section 5.1 allows ("Integer encodings that exceed implementation
    limits -- in value or octet length -- MUST be treated as decoding
    errors"). -/
def decodeIntUpTo (n max : Nat) (b : List UInt8) : Option (Nat × List UInt8) :=
  match decodeInt n b with
  | some (i, rest) => if i ≤ max then some (i, rest) else none
  | none => none

/-! ## The Huffman code (section 5.2, Appendix B) -/

/-- The column "code as hex aligned to LSB" of Appendix B, with the
    length of each code: the octets 0 to 255, then EOS (256). -/
def huffmanTable : List (Nat × Nat) :=
  [(0x1ff8, 13), (0x7fffd8, 23), (0xfffffe2, 28), (0xfffffe3, 28), (0xfffffe4, 28), (0xfffffe5, 28),
   (0xfffffe6, 28), (0xfffffe7, 28), (0xfffffe8, 28), (0xffffea, 24), (0x3ffffffc, 30), (0xfffffe9, 28),
   (0xfffffea, 28), (0x3ffffffd, 30), (0xfffffeb, 28), (0xfffffec, 28), (0xfffffed, 28), (0xfffffee, 28),
   (0xfffffef, 28), (0xffffff0, 28), (0xffffff1, 28), (0xffffff2, 28), (0x3ffffffe, 30), (0xffffff3, 28),
   (0xffffff4, 28), (0xffffff5, 28), (0xffffff6, 28), (0xffffff7, 28), (0xffffff8, 28), (0xffffff9, 28),
   (0xffffffa, 28), (0xffffffb, 28), (0x14, 6), (0x3f8, 10), (0x3f9, 10), (0xffa, 12),
   (0x1ff9, 13), (0x15, 6), (0xf8, 8), (0x7fa, 11), (0x3fa, 10), (0x3fb, 10),
   (0xf9, 8), (0x7fb, 11), (0xfa, 8), (0x16, 6), (0x17, 6), (0x18, 6),
   (0x0, 5), (0x1, 5), (0x2, 5), (0x19, 6), (0x1a, 6), (0x1b, 6),
   (0x1c, 6), (0x1d, 6), (0x1e, 6), (0x1f, 6), (0x5c, 7), (0xfb, 8),
   (0x7ffc, 15), (0x20, 6), (0xffb, 12), (0x3fc, 10), (0x1ffa, 13), (0x21, 6),
   (0x5d, 7), (0x5e, 7), (0x5f, 7), (0x60, 7), (0x61, 7), (0x62, 7),
   (0x63, 7), (0x64, 7), (0x65, 7), (0x66, 7), (0x67, 7), (0x68, 7),
   (0x69, 7), (0x6a, 7), (0x6b, 7), (0x6c, 7), (0x6d, 7), (0x6e, 7),
   (0x6f, 7), (0x70, 7), (0x71, 7), (0x72, 7), (0xfc, 8), (0x73, 7),
   (0xfd, 8), (0x1ffb, 13), (0x7fff0, 19), (0x1ffc, 13), (0x3ffc, 14), (0x22, 6),
   (0x7ffd, 15), (0x3, 5), (0x23, 6), (0x4, 5), (0x24, 6), (0x5, 5),
   (0x25, 6), (0x26, 6), (0x27, 6), (0x6, 5), (0x74, 7), (0x75, 7),
   (0x28, 6), (0x29, 6), (0x2a, 6), (0x7, 5), (0x2b, 6), (0x76, 7),
   (0x2c, 6), (0x8, 5), (0x9, 5), (0x2d, 6), (0x77, 7), (0x78, 7),
   (0x79, 7), (0x7a, 7), (0x7b, 7), (0x7ffe, 15), (0x7fc, 11), (0x3ffd, 14),
   (0x1ffd, 13), (0xffffffc, 28), (0xfffe6, 20), (0x3fffd2, 22), (0xfffe7, 20), (0xfffe8, 20),
   (0x3fffd3, 22), (0x3fffd4, 22), (0x3fffd5, 22), (0x7fffd9, 23), (0x3fffd6, 22), (0x7fffda, 23),
   (0x7fffdb, 23), (0x7fffdc, 23), (0x7fffdd, 23), (0x7fffde, 23), (0xffffeb, 24), (0x7fffdf, 23),
   (0xffffec, 24), (0xffffed, 24), (0x3fffd7, 22), (0x7fffe0, 23), (0xffffee, 24), (0x7fffe1, 23),
   (0x7fffe2, 23), (0x7fffe3, 23), (0x7fffe4, 23), (0x1fffdc, 21), (0x3fffd8, 22), (0x7fffe5, 23),
   (0x3fffd9, 22), (0x7fffe6, 23), (0x7fffe7, 23), (0xffffef, 24), (0x3fffda, 22), (0x1fffdd, 21),
   (0xfffe9, 20), (0x3fffdb, 22), (0x3fffdc, 22), (0x7fffe8, 23), (0x7fffe9, 23), (0x1fffde, 21),
   (0x7fffea, 23), (0x3fffdd, 22), (0x3fffde, 22), (0xfffff0, 24), (0x1fffdf, 21), (0x3fffdf, 22),
   (0x7fffeb, 23), (0x7fffec, 23), (0x1fffe0, 21), (0x1fffe1, 21), (0x3fffe0, 22), (0x1fffe2, 21),
   (0x7fffed, 23), (0x3fffe1, 22), (0x7fffee, 23), (0x7fffef, 23), (0xfffea, 20), (0x3fffe2, 22),
   (0x3fffe3, 22), (0x3fffe4, 22), (0x7ffff0, 23), (0x3fffe5, 22), (0x3fffe6, 22), (0x7ffff1, 23),
   (0x3ffffe0, 26), (0x3ffffe1, 26), (0xfffeb, 20), (0x7fff1, 19), (0x3fffe7, 22), (0x7ffff2, 23),
   (0x3fffe8, 22), (0x1ffffec, 25), (0x3ffffe2, 26), (0x3ffffe3, 26), (0x3ffffe4, 26), (0x7ffffde, 27),
   (0x7ffffdf, 27), (0x3ffffe5, 26), (0xfffff1, 24), (0x1ffffed, 25), (0x7fff2, 19), (0x1fffe3, 21),
   (0x3ffffe6, 26), (0x7ffffe0, 27), (0x7ffffe1, 27), (0x3ffffe7, 26), (0x7ffffe2, 27), (0xfffff2, 24),
   (0x1fffe4, 21), (0x1fffe5, 21), (0x3ffffe8, 26), (0x3ffffe9, 26), (0xffffffd, 28), (0x7ffffe3, 27),
   (0x7ffffe4, 27), (0x7ffffe5, 27), (0xfffec, 20), (0xfffff3, 24), (0xfffed, 20), (0x1fffe6, 21),
   (0x3fffe9, 22), (0x1fffe7, 21), (0x1fffe8, 21), (0x7ffff3, 23), (0x3fffea, 22), (0x3fffeb, 22),
   (0x1ffffee, 25), (0x1ffffef, 25), (0xfffff4, 24), (0xfffff5, 24), (0x3ffffea, 26), (0x7ffff4, 23),
   (0x3ffffeb, 26), (0x7ffffe6, 27), (0x3ffffec, 26), (0x3ffffed, 26), (0x7ffffe7, 27), (0x7ffffe8, 27),
   (0x7ffffe9, 27), (0x7ffffea, 27), (0x7ffffeb, 27), (0xffffffe, 28), (0x7ffffec, 27), (0x7ffffed, 27),
   (0x7ffffee, 27), (0x7ffffef, 27), (0x7fffff0, 27), (0x3ffffee, 26), (0x3fffffff, 30)]

/-- `len` bits of `x`, most significant first. -/
def toBits (x len : Nat) : List Bool :=
  (List.range len).reverse.map fun k => x / 2 ^ k % 2 == 1

/-- The code of each symbol as bits, in symbol order. -/
def codes : List (List Bool) :=
  huffmanTable.map fun (code, len) => toBits code len

/-- The code of an octet, as bits. -/
def symbolBits (c : UInt8) : List Bool := codes.getD c.toNat []

/-- Octets from bits, eight at a time, most significant first. Bits
    left over at the end are dropped. -/
def ofBits : List Bool → List UInt8
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: rest =>
    ([b7, b6, b5, b4, b3, b2, b1, b0].foldl (fun acc (b : Bool) => 2 * acc + if b then 1 else 0) 0).toUInt8
      :: ofBits rest
  | _ => []

/-- The Huffman encoding of `s`: the codes of its octets, then ones to
    the next octet boundary. -/
def huffmanEncode (s : List UInt8) : List UInt8 :=
  let bits := s.flatMap symbolBits
  ofBits (bits ++ List.replicate ((8 - bits.length % 8) % 8) true)

/-- The symbol whose code is `bits`, if there is one. -/
def symbolOf (bits : List Bool) : Option Nat := codes.findIdx? (· == bits)

/-- Decodes bits, with `pending` the bits read since the last symbol. -/
def decodeBits : List Bool → List Bool → Option (List UInt8)
  | [], pending => if pending.length < 8 ∧ pending.all (· == true) then some [] else none
  | b :: bs, pending =>
    let pending := pending ++ [b]
    match symbolOf pending with
    | some s =>
      if s = 256 then none
      else match decodeBits bs [] with
        | some out => some (s.toUInt8 :: out)
        | none => none
    | none => decodeBits bs pending

/-- The octets whose Huffman encoding is `d`, or `none` when `d` is not
    one: it holds EOS, or ends in more than seven bits of padding, or in
    padding that is not all ones. -/
def huffmanDecode (d : List UInt8) : Option (List UInt8) :=
  decodeBits (d.flatMap fun b => toBits b.toNat 8) []

/-! ## String literals (section 5.2) -/

/-- A string literal for `s`: Huffman encoded when `huffman` is true,
    else the octets as they are. -/
def encodeString (huffman : Bool) (s : List UInt8) : List UInt8 :=
  if huffman then
    let d := huffmanEncode s
    encodeInt 7 1 d.length ++ d
  else encodeInt 7 0 s.length ++ s

/-- The string literal at the start of the input, decoded, and the
    octets after it. -/
def decodeString : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: bs =>
    match decodeInt 7 (b :: bs) with
    | none => none
    | some (len, rest) =>
      if len ≤ rest.length then
        if b.toNat < 128 then some (rest.take len, rest.drop len)
        else match huffmanDecode (rest.take len) with
          | some s => some (s, rest.drop len)
          | none => none
      else none

/-! ## The static table (Appendix A) -/

/-- Table 1 of Appendix A, in index order from 1. -/
def staticTable : List (String × String) :=
  [(":authority", ""),
   (":method", "GET"),
   (":method", "POST"),
   (":path", "/"),
   (":path", "/index.html"),
   (":scheme", "http"),
   (":scheme", "https"),
   (":status", "200"),
   (":status", "204"),
   (":status", "206"),
   (":status", "304"),
   (":status", "400"),
   (":status", "404"),
   (":status", "500"),
   ("accept-charset", ""),
   ("accept-encoding", "gzip, deflate"),
   ("accept-language", ""),
   ("accept-ranges", ""),
   ("accept", ""),
   ("access-control-allow-origin", ""),
   ("age", ""),
   ("allow", ""),
   ("authorization", ""),
   ("cache-control", ""),
   ("content-disposition", ""),
   ("content-encoding", ""),
   ("content-language", ""),
   ("content-length", ""),
   ("content-location", ""),
   ("content-range", ""),
   ("content-type", ""),
   ("cookie", ""),
   ("date", ""),
   ("etag", ""),
   ("expect", ""),
   ("expires", ""),
   ("from", ""),
   ("host", ""),
   ("if-match", ""),
   ("if-modified-since", ""),
   ("if-none-match", ""),
   ("if-range", ""),
   ("if-unmodified-since", ""),
   ("last-modified", ""),
   ("link", ""),
   ("location", ""),
   ("max-forwards", ""),
   ("proxy-authenticate", ""),
   ("proxy-authorization", ""),
   ("range", ""),
   ("referer", ""),
   ("refresh", ""),
   ("retry-after", ""),
   ("server", ""),
   ("set-cookie", ""),
   ("strict-transport-security", ""),
   ("transfer-encoding", ""),
   ("user-agent", ""),
   ("vary", ""),
   ("via", ""),
   ("www-authenticate", "")]

/-- The name and value at an index of the static table, from 1 to 61. -/
def staticEntry (i : Nat) : Option (String × String) :=
  if i = 0 then none else staticTable[i - 1]?

end Hpack
