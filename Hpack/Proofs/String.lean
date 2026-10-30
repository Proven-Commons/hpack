/-
  String literals (RFC 7541, section 5.2), the static table
  (Appendix A), and the limit on integers.
-/

import Hpack.Spec.Defs
import Hpack
import Hpack.Proofs.Int
import Hpack.Proofs.Huffman

namespace HpackProofs

open Hpack

/-! ### Integers with a limit -/

theorem decodeIntUpTo_iff (n max : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    decodeIntUpTo n max b = some (i, rest) ↔
      i ≤ max ∧ ∃ high, high < 2 ^ (8 - n) ∧ b = Hpack.Spec.intEncode n high i ++ rest := by
  rw [← decodeInt_iff n b i rest hn]
  unfold decodeIntUpTo
  constructor
  · intro h
    split at h
    · rename_i i' rest' hd
      split at h
      · rename_i hle
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hle, hd⟩
      · contradiction
    · contradiction
  · rintro ⟨hle, hd⟩
    rw [hd]
    simp [hle]

/-! ### The first octet of a string literal -/

/-- With a 7-bit prefix, the first octet is the H flag and seven bits. -/
theorem intEncode_seven (high i : Nat) (_hh : high < 2) :
    ∃ o tl, o < 128 ∧ Hpack.Spec.intEncode 7 high i = (high * 128 + o).toUInt8 :: tl := by
  unfold Hpack.Spec.intEncode Hpack.Spec.intOctets
  by_cases h : i < 2 ^ 7 - 1
  · exact ⟨i, [], by omega, by simp [h]⟩
  · refine ⟨127, (Hpack.Spec.intOctets.rest (i - (2 ^ 7 - 1))).map Nat.toUInt8, by omega, ?_⟩
    simp [h]

theorem first_octet (high o : Nat) (hh : high < 2) (ho : o < 128) :
    (high * 128 + o).toUInt8.toNat < 128 ↔ high = 0 := by
  rw [toNat_toUInt8 (by omega)]
  omega

/-! ### The statements -/

theorem encodeString_spec (huffman : Bool) (s : List UInt8) :
    Hpack.Spec.StringLiteral huffman s (encodeString huffman s) := by
  cases huffman
  · simp only [Hpack.Spec.StringLiteral, encodeString, Bool.false_eq_true, ↓reduceIte]
    rw [encodeInt_eq 7 0 s.length (by omega) (by decide)]
  · simp only [Hpack.Spec.StringLiteral, encodeString, ↓reduceIte]
    exact ⟨huffmanEncode s, huffmanEncode_spec s,
      by rw [encodeInt_eq 7 1 _ (by omega) (by decide)]⟩

theorem decodeString_iff (b s rest : List UInt8) :
    decodeString b = some (s, rest) ↔
      ∃ huffman lit, Hpack.Spec.StringLiteral huffman s lit ∧ b = lit ++ rest := by
  constructor
  · intro h
    cases b with
    | nil => simp [decodeString] at h
    | cons p bs =>
      simp only [decodeString] at h
      split at h
      · contradiction
      · rename_i len r hd
        obtain ⟨high, hhigh, he⟩ := (decodeInt_iff 7 (p :: bs) len r (by omega)).mp hd
        have hhigh' : high < 2 := by simpa using hhigh
        obtain ⟨o, tl, ho, hx⟩ := intEncode_seven high len hhigh'
        have hp : p = (high * 128 + o).toUInt8 := by
          rw [hx, List.cons_append] at he
          exact (List.cons.inj he).1
        have hfirst := first_octet high o hhigh' ho
        rw [← hp] at hfirst
        split at h
        · rename_i hlen
          split at h
          · rename_i hraw
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have h0 : high = 0 := hfirst.mp hraw
            subst h0
            refine ⟨false, Hpack.Spec.intEncode 7 0 len ++ r.take len, ?_, ?_⟩
            · simp only [Hpack.Spec.StringLiteral, Bool.false_eq_true, ↓reduceIte]
              simp [hlen]
            · rw [he, List.append_assoc, List.take_append_drop]
          · rename_i hraw
            split at h
            · rename_i s' hs
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have h1 : high = 1 := by
                have : ¬ high = 0 := fun h0 => hraw (hfirst.mpr h0)
                omega
              subst h1
              refine ⟨true, Hpack.Spec.intEncode 7 1 len ++ r.take len, ?_, ?_⟩
              · simp only [Hpack.Spec.StringLiteral, ↓reduceIte]
                refine ⟨r.take len, (huffmanDecode_iff _ _).mp hs, ?_⟩
                simp [hlen]
              · rw [he, List.append_assoc, List.take_append_drop]
            · contradiction
        · contradiction
  · rintro ⟨huffman, lit, hlit, rfl⟩
    cases huffman
    · simp only [Hpack.Spec.StringLiteral, Bool.false_eq_true, ↓reduceIte] at hlit
      subst hlit
      obtain ⟨o, tl, ho, hx⟩ := intEncode_seven 0 s.length (by omega)
      have hd : decodeInt 7 (Hpack.Spec.intEncode 7 0 s.length ++ (s ++ rest)) =
          some (s.length, s ++ rest) :=
        (decodeInt_iff 7 _ _ _ (by omega)).mpr ⟨0, by decide, rfl⟩
      have hraw : ((0 * 128 + o).toUInt8).toNat < 128 := (first_octet 0 o (by omega) ho).mpr rfl
      rw [List.append_assoc]
      rw [hx, List.cons_append] at hd ⊢
      simp only [decodeString, hd, hraw, ↓reduceIte]
      simp
    · simp only [Hpack.Spec.StringLiteral, ↓reduceIte] at hlit
      obtain ⟨d, hdl, rfl⟩ := hlit
      obtain ⟨o, tl, ho, hx⟩ := intEncode_seven 1 d.length (by omega)
      have hd : decodeInt 7 (Hpack.Spec.intEncode 7 1 d.length ++ (d ++ rest)) =
          some (d.length, d ++ rest) :=
        (decodeInt_iff 7 _ _ _ (by omega)).mpr ⟨1, by decide, rfl⟩
      have hraw : ¬ ((1 * 128 + o).toUInt8).toNat < 128 := fun h =>
        absurd ((first_octet 1 o (by omega) ho).mp h) (by omega)
      have hs : huffmanDecode d = some s := (huffmanDecode_iff d s).mpr hdl
      rw [List.append_assoc]
      rw [hx, List.cons_append] at hd ⊢
      simp only [decodeString, hd, hraw, ↓reduceIte]
      simp [hs]

theorem decodeString_encode (huffman : Bool) (s rest : List UInt8) :
    decodeString (encodeString huffman s ++ rest) = some (s, rest) :=
  (decodeString_iff _ _ _).mpr ⟨huffman, _, encodeString_spec huffman s, rfl⟩

/-! ### The static table -/

theorem staticTable_eq_b : (Hpack.staticTable == Hpack.Spec.staticTable) = true := by decide +kernel

theorem staticEntry_eq (i : Nat) :
    staticEntry i = if i = 0 then none else Hpack.Spec.staticTable[i - 1]? := by
  unfold staticEntry
  rw [beq_iff_eq.mp staticTable_eq_b]

end HpackProofs
