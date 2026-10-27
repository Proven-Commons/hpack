/-
  Command line front end.

    hpack huffman-encode TEXT
    hpack huffman-decode HEX
    hpack string-decode HEX

  print the Huffman encoding of a text in hex, the text a Huffman
  encoding decodes to, or the octets of the string literal at the start
  of some octets and the hex of what follows. They exit with 1 when the
  input does not decode.

    hpack serve

  answers requests on standard input, one per line, for the
  differential tests. Octets are sent as hex digits, two per octet, and
  an empty field is written `-`. Numbers are decimal.

    int N HEX               prints  OK, the value and the hex of the rest,
                                    or FAIL               (decodeInt)
    intmax N MAX HEX        the same, with a limit        (decodeIntUpTo)
    encint N HIGH VALUE     prints  OK and the hex        (encodeInt)
    huffdec HEX             prints  OK and the hex of the octets, or FAIL
    huffenc HEX             prints  OK and the hex
    strdec HEX              prints  OK, the hex of the octets and the hex
                                    of the rest, or FAIL  (decodeString)
    strenc H HEX            prints  OK and the hex, with H 0 or 1
                                                          (encodeString)
    static I                prints  OK and the hex of the name and the
                                    value, or FAIL        (staticEntry)

  A malformed request prints `error`: an unknown operation, the wrong
  number of fields, hex digits that are not in pairs, a number that is
  not decimal, a prefix size outside 1 to 8, or bits above the prefix
  that do not fit. A request line may end in LF or CR LF.

  Every answer comes from the proved functions in `Hpack/`. The hex
  coding and the request handling here are covered by the tests, not by
  a proof.
-/

import Hpack

open Hpack

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The octets a field gives: `-` for none, else hex digits in pairs. -/
def fromHex (f : String) : Option (List UInt8) :=
  if f = "-" then some [] else if f.isEmpty then none else hexBytes f.toList

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A field for a list of octets: `-` when it is empty. -/
def toHex (bs : List UInt8) : String :=
  if bs.isEmpty then "-"
  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- A decimal number, without sign or leading `+`. -/
def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-- A prefix size, from 1 to 8. -/
def prefixSize (s : String) : Option Nat := do
  let n ← decimal s
  if 1 ≤ n ∧ n ≤ 8 then some n else none

def utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["int", n, h] => do
    let n ← prefixSize n
    let b ← fromHex h
    pure (match decodeInt n b with
      | some (i, rest) => s!"OK {i} {toHex rest}"
      | none => "FAIL")
  | ["intmax", n, m, h] => do
    let n ← prefixSize n
    let m ← decimal m
    let b ← fromHex h
    pure (match decodeIntUpTo n m b with
      | some (i, rest) => s!"OK {i} {toHex rest}"
      | none => "FAIL")
  | ["encint", n, high, v] => do
    let n ← prefixSize n
    let high ← decimal high
    let v ← decimal v
    if high < 2 ^ (8 - n) then pure s!"OK {toHex (encodeInt n high v)}" else none
  | ["huffdec", h] => do
    let d ← fromHex h
    pure (match huffmanDecode d with
      | some s => s!"OK {toHex s}"
      | none => "FAIL")
  | ["huffenc", h] => do
    let s ← fromHex h
    pure s!"OK {toHex (huffmanEncode s)}"
  | ["strdec", h] => do
    let b ← fromHex h
    pure (match decodeString b with
      | some (s, rest) => s!"OK {toHex s} {toHex rest}"
      | none => "FAIL")
  | ["strenc", flag, h] => do
    let huffman ← match flag with
      | "0" => some false
      | "1" => some true
      | _ => none
    let s ← fromHex h
    pure s!"OK {toHex (encodeString huffman s)}"
  | ["static", i] => do
    let i ← decimal i
    pure (match staticEntry i with
      | some (name, value) => s!"OK {toHex (utf8 name)} {toHex (utf8 value)}"
      | none => "FAIL")
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")
    stdout.flush

def usage : String :=
  "usage: hpack huffman-encode TEXT\n       hpack huffman-decode HEX\n" ++
  "       hpack string-decode HEX\n       hpack serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["huffman-encode", text] =>
    IO.println (toHex (huffmanEncode (utf8 text)))
    return 0
  | ["huffman-decode", h] =>
    match (fromHex h).bind huffmanDecode with
    | some s => IO.println (toHex s); return 0
    | none => IO.eprintln "not a Huffman encoding"; return 1
  | ["string-decode", h] =>
    match (fromHex h).bind decodeString with
    | some (s, rest) => IO.println s!"{toHex s} {toHex rest}"; return 0
    | none => IO.eprintln "not a string literal"; return 1
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
