/-
  Integers with an N-bit prefix (RFC 7541, section 5.1).
-/

import Hpack.Spec.Defs
import Hpack

namespace HpackProofs

open Hpack

theorem toNat_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt b

theorem toNat_toUInt8 {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp; omega

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by simp

/-! ### The octets after the prefix -/

theorem encodeRest_eq (j : Nat) : encodeRest j = (Hpack.Spec.intOctets.rest j).map Nat.toUInt8 := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [encodeRest, Hpack.Spec.intOctets.rest]
    by_cases h : j < 128
    · simp [h, show ¬ j ≥ 128 by omega]
    · simp [h, show j ≥ 128 by omega, ih (j / 128) (by omega)]

/-- `decodeRest` as it was first written: one octet at a time, the
    value built from the last octet back. The proofs are about this form,
    and `decodeRest_eq_rec` shows that the code computes the same. -/
def decodeRestRec : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else match decodeRestRec bs with
      | some (j, rest) => if j = 0 then none else some (b.toNat - 128 + 128 * j, rest)
      | none => none

/-- The digits `splitRest` gives, most significant first, without the
    accumulator. -/
def splitRestRec : List UInt8 → Option (List Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some ([b.toNat], bs)
    else (splitRestRec bs).map fun (ds, r) => (ds ++ [b.toNat % 128], r)

theorem splitRest_eq (bs : List UInt8) (acc : List Nat) :
    splitRest bs acc = (splitRestRec bs).map fun (ds, r) => (ds ++ acc, r) := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [splitRest, splitRestRec]
    split
    · rfl
    · rw [ih]
      cases splitRestRec bs <;> simp

theorem splitRestRec_ne_nil {bs : List UInt8} {ds : List Nat} {r : List UInt8}
    (h : splitRestRec bs = some (ds, r)) : ds ≠ [] := by
  induction bs generalizing ds r with
  | nil => simp [splitRestRec] at h
  | cons b bs ih =>
    simp only [splitRestRec] at h
    split at h
    · cases h
      simp
    · cases hs : splitRestRec bs with
      | none => simp [hs] at h
      | some p =>
        obtain ⟨ds', r'⟩ := p
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        simp

/-- The value of digits in base `2 ^ w`, most significant first, one
    digit at a time. -/
def digitsVal (w : Nat) (ds : List Nat) : Nat := ds.foldl (fun j d => j * 2 ^ w + d) 0

theorem foldl_digits (w : Nat) (ds : List Nat) (a : Nat) :
    ds.foldl (fun j d => j * 2 ^ w + d) a = a * 2 ^ (w * ds.length) + digitsVal w ds := by
  induction ds generalizing a with
  | nil => simp [digitsVal]
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons, digitsVal]
    rw [ih, ih (0 * 2 ^ w + d)]
    rw [Nat.mul_succ, Nat.pow_add, Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc,
      Nat.mul_comm (2 ^ w) (2 ^ (w * ds.length)), Nat.add_assoc]

theorem digitsVal_append (w : Nat) (l1 l2 : List Nat) :
    digitsVal w (l1 ++ l2) = digitsVal w l1 * 2 ^ (w * l2.length) + digitsVal w l2 := by
  unfold digitsVal
  rw [List.foldl_append, foldl_digits]
  rfl

theorem ofDigits_go (w fuel : Nat) (ds : List Nat) (h : ds.length ≤ fuel) :
    ofDigits.go w fuel ds = digitsVal w ds := by
  induction fuel generalizing ds with
  | zero =>
    have : ds = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ fuel ih =>
    unfold ofDigits.go
    split
    · rfl
    · rename_i hl
      simp only [Nat.shiftLeft_eq]
      rw [ih _ (by simp; omega), ih _ (by simp; omega)]
      conv => rhs; rw [← List.take_append_drop (ds.length / 2) ds]
      rw [digitsVal_append, List.length_drop]

theorem ofDigits_eq (w : Nat) (ds : List Nat) : ofDigits w ds = digitsVal w ds :=
  ofDigits_go w _ ds (Nat.le_refl _)

theorem digitsVal_cons_pos (w last : Nat) (more : List Nat) (h : last ≠ 0) :
    digitsVal w (last :: more) ≠ 0 := by
  have := digitsVal_append w [last] more
  simp only [List.singleton_append] at this
  rw [this]
  have : digitsVal w [last] = last := by simp [digitsVal]
  rw [this]
  have := Nat.two_pow_pos (w * more.length)
  have : last * 2 ^ (w * more.length) ≠ 0 := Nat.mul_ne_zero h (by omega)
  omega

theorem decodeRest_split (bs : List UInt8) :
    (match splitRestRec bs with
      | some (last :: more, rest) =>
        if last = 0 ∧ more ≠ [] then none else some (digitsVal 7 (last :: more), rest)
      | _ => none) = decodeRestRec bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := toNat_lt b
    by_cases hb128 : b.toNat < 128
    · simp [splitRestRec, decodeRestRec, hb128, digitsVal]
    · simp only [splitRestRec, decodeRestRec, hb128, ↓reduceIte]
      cases hs : splitRestRec bs with
      | none =>
        rw [hs] at ih
        simp only at ih
        rw [← ih]
        simp
      | some p =>
        obtain ⟨ds, r⟩ := p
        have hne := splitRestRec_ne_nil hs
        obtain ⟨last, more, rfl⟩ := List.exists_cons_of_ne_nil hne
        rw [hs] at ih
        simp only at ih
        rw [← ih]
        simp only [Option.map_some, List.cons_append]
        by_cases hl : last = 0
        · subst hl
          by_cases hm : more = []
          · subst hm
            simp [digitsVal]
          · simp [hm]
        · have hpos := digitsVal_cons_pos 7 last more hl
          simp only [hl, false_and, ↓reduceIte, ne_eq, hpos]
          rw [show last :: (more ++ [b.toNat % 128]) = (last :: more) ++ [b.toNat % 128] by rfl,
            digitsVal_append]
          simp only [List.length_singleton, Nat.mul_one, Option.some.injEq, Prod.mk.injEq, and_true]
          have : digitsVal 7 [b.toNat % 128] = b.toNat % 128 := by simp [digitsVal]
          rw [this]
          omega

theorem decodeRest_eq_rec (bs : List UInt8) : decodeRest bs = decodeRestRec bs := by
  rw [← decodeRest_split]
  unfold decodeRest
  rw [splitRest_eq]
  cases splitRestRec bs with
  | none => rfl
  | some p =>
    obtain ⟨ds, r⟩ := p
    simp only [Option.map_some, List.append_nil]
    split <;> simp_all [ofDigits_eq]

theorem decodeRestRec_encodeRest (j : Nat) (rest : List UInt8) :
    decodeRestRec (encodeRest j ++ rest) = some (j, rest) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [encodeRest]
    by_cases h : j < 128
    · simp only [h, ↓reduceIte, List.singleton_append, decodeRestRec, toNat_toUInt8 (by omega : j < 256)]
    · simp only [h, ↓reduceIte, List.cons_append, decodeRestRec,
        toNat_toUInt8 (by omega : j % 128 + 128 < 256)]
      rw [ih (j / 128) (by omega)]
      simp only [show ¬ (j % 128 + 128 < 128) by omega, ↓reduceIte,
        show ¬ (j / 128 = 0) by omega]
      congr 2
      omega

theorem eq_of_decodeRestRec {bs : List UInt8} {j : Nat} {rest : List UInt8}
    (h : decodeRestRec bs = some (j, rest)) : bs = encodeRest j ++ rest := by
  induction bs generalizing j with
  | nil => simp [decodeRestRec] at h
  | cons b bs ih =>
    simp only [decodeRestRec] at h
    split at h
    · rename_i hb
      cases h
      rw [encodeRest]
      simp [hb]
    · rename_i hb
      split at h
      · rename_i j' rest' hj'
        split at h
        · contradiction
        · rename_i hj0
          cases h
          have := ih hj'
          subst this
          have hb' := toNat_lt b
          rw [encodeRest.eq_1 (b.toNat - 128 + 128 * j')]
          simp only [show ¬ (b.toNat - 128 + 128 * j' < 128) by omega, ↓reduceIte, List.cons_append]
          congr 1
          · apply UInt8.toNat_inj.mp
            rw [toNat_toUInt8 (by omega)]
            omega
          · congr 2
            omega
      · contradiction

theorem decodeRest_encodeRest (j : Nat) (rest : List UInt8) :
    decodeRest (encodeRest j ++ rest) = some (j, rest) := by
  rw [decodeRest_eq_rec, decodeRestRec_encodeRest]

theorem eq_of_decodeRest {bs : List UInt8} {j : Nat} {rest : List UInt8}
    (h : decodeRest bs = some (j, rest)) : bs = encodeRest j ++ rest := by
  rw [decodeRest_eq_rec] at h
  exact eq_of_decodeRestRec h

theorem decodeRest_iff (bs : List UInt8) (j : Nat) (rest : List UInt8) :
    decodeRest bs = some (j, rest) ↔ bs = encodeRest j ++ rest :=
  ⟨eq_of_decodeRest, fun h => h ▸ decodeRest_encodeRest j rest⟩

/-! ### The first octet -/

theorem prefix_cases (n : Nat) (hn : 1 ≤ n ∧ n ≤ 8) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega

/-- The first octet, written from the bits above the prefix and the
    prefix. -/
theorem first_toNat (n high o : Nat) (hn : 1 ≤ n ∧ n ≤ 8) (hh : high < 2 ^ (8 - n))
    (ho : o < 2 ^ n) :
    (high * 2 ^ n + o).toUInt8.toNat = high * 2 ^ n + o ∧
    (high * 2 ^ n + o) % 2 ^ n = o ∧ (high * 2 ^ n + o) / 2 ^ n = high := by
  rcases prefix_cases n hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] at hh ho ⊢ <;>
    refine ⟨toNat_toUInt8 (by omega), by omega, by omega⟩

/-- Every octet is some bits above the prefix and a prefix. -/
theorem octet_split (n : Nat) (hn : 1 ≤ n ∧ n ≤ 8) (b : UInt8) :
    b.toNat / 2 ^ n < 2 ^ (8 - n) ∧ b.toNat = b.toNat / 2 ^ n * 2 ^ n + b.toNat % 2 ^ n := by
  have := toNat_lt b
  rcases prefix_cases n hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceSub] <;> omega

theorem pow_pos' (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem decodeInt_nil (n : Nat) : decodeInt n [] = none := by
  unfold decodeInt
  split <;> rfl

theorem decodeInt_cons (n : Nat) (hn : 1 ≤ n ∧ n ≤ 8) (p : UInt8) (bs : List UInt8) :
    decodeInt n (p :: bs) =
      if p.toNat % 2 ^ n < 2 ^ n - 1 then some (p.toNat % 2 ^ n, bs)
      else match decodeRest bs with
        | some (j, rest) => some (2 ^ n - 1 + j, rest)
        | none => none := by
  unfold decodeInt
  simp only [show ¬(n = 0 ∨ 8 < n) by omega, ↓reduceIte]
  rfl

theorem decodeInt_prefix (n max : Nat) (b : List UInt8) (hn : n = 0 ∨ 8 < n) :
    decodeInt n b = none ∧ decodeIntUpTo n max b = none := by
  have h : decodeInt n b = none := by
    unfold decodeInt
    simp only [hn, ↓reduceIte]
  refine ⟨h, ?_⟩
  unfold decodeIntUpTo
  rw [h]

/-! ### The statements -/

theorem encodeInt_eq (n high i : Nat) (_hn : 1 ≤ n ∧ n ≤ 8) (hhigh : high < 2 ^ (8 - n)) :
    encodeInt n high i = Hpack.Spec.intEncode n high i := by
  have hmod : high % 2 ^ (8 - n) = high := Nat.mod_eq_of_lt hhigh
  unfold encodeInt Hpack.Spec.intEncode Hpack.Spec.intOctets
  rw [hmod]
  by_cases h : i < 2 ^ n - 1
  · simp [h]
  · simp [h, encodeRest_eq]

theorem decodeInt_iff (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    decodeInt n b = some (i, rest) ↔
      ∃ high, high < 2 ^ (8 - n) ∧ b = Hpack.Spec.intEncode n high i ++ rest := by
  have hpos := pow_pos' n
  constructor
  · intro h
    cases b with
    | nil => simp [decodeInt_nil] at h
    | cons p bs =>
      obtain ⟨hhigh, hsplit⟩ := octet_split n hn p
      refine ⟨p.toNat / 2 ^ n, hhigh, ?_⟩
      rw [← encodeInt_eq n _ i hn hhigh]
      rw [decodeInt_cons n hn] at h
      unfold encodeInt
      rw [Nat.mod_eq_of_lt hhigh]
      by_cases hp : p.toNat % 2 ^ n < 2 ^ n - 1
      · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [hp, ↓reduceIte, List.singleton_append]
        congr 1
        apply UInt8.toNat_inj.mp
        rw [← hsplit, toUInt8_toNat]
      · simp only [hp, ↓reduceIte] at h
        split at h
        · rename_i j rest' hj
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [decodeRest_iff] at hj
          subst hj
          simp only [show ¬ (2 ^ n - 1 + j < 2 ^ n - 1) by omega, ↓reduceIte, List.cons_append]
          congr 1
          · have : p.toNat % 2 ^ n = 2 ^ n - 1 := by
              have := Nat.mod_lt p.toNat hpos
              omega
            rw [← this, ← hsplit, toUInt8_toNat]
          · congr 2
            omega
        · contradiction
  · rintro ⟨high, hhigh, rfl⟩
    rw [← encodeInt_eq n high i hn hhigh]
    unfold encodeInt
    rw [Nat.mod_eq_of_lt hhigh]
    by_cases h : i < 2 ^ n - 1
    · obtain ⟨h1, h2, _⟩ := first_toNat n high i hn hhigh (by omega)
      simp only [h, ↓reduceIte, List.singleton_append, decodeInt_cons n hn, h1, h2]
    · obtain ⟨h1, h2, _⟩ := first_toNat n high (2 ^ n - 1) hn hhigh (by omega)
      simp only [h, ↓reduceIte, List.cons_append, decodeInt_cons n hn, h1, h2, Nat.lt_irrefl,
        decodeRest_encodeRest]
      congr 2
      omega

/-! ### Against the decoding pseudocode -/

theorem loop_encodeRest (j : Nat) (rest : List UInt8) (acc m : Nat) :
    Hpack.Spec.intDecode.loop (encodeRest j ++ rest) acc m = some (acc + j * 2 ^ m, rest) := by
  induction j using Nat.strongRecOn generalizing acc m with
  | ind j ih =>
    rw [encodeRest]
    by_cases h : j < 128
    · simp only [h, ↓reduceIte, List.singleton_append, Hpack.Spec.intDecode.loop,
        toNat_toUInt8 (by omega : j < 256)]
      simp [show j / 128 = 0 by omega, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceIte, List.cons_append, Hpack.Spec.intDecode.loop,
        toNat_toUInt8 (by omega : j % 128 + 128 < 256)]
      simp only [show (j % 128 + 128) / 128 = 1 by omega, ↓reduceIte,
        show (j % 128 + 128) % 128 = j % 128 by omega]
      rw [ih (j / 128) (by omega)]
      congr 2
      conv => rhs; rw [← Nat.mod_add_div j 128]
      simp only [Nat.pow_add, Nat.reducePow, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add,
        Nat.add_assoc]

theorem decodeInt_rfc (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    decodeInt n b = some (i, rest) → Hpack.Spec.intDecode n b = some (i, rest) := by
  intro h
  obtain ⟨high, hhigh, rfl⟩ := (decodeInt_iff n b i rest hn).mp h
  have hpos := pow_pos' n
  unfold Hpack.Spec.intEncode Hpack.Spec.intOctets
  by_cases hi : i < 2 ^ n - 1
  · obtain ⟨h1, h2, _⟩ := first_toNat n high i hn hhigh (by omega)
    simp only [hi, ↓reduceIte, List.map_nil, List.singleton_append, Hpack.Spec.intDecode, h1, h2]
  · obtain ⟨h1, h2, _⟩ := first_toNat n high (2 ^ n - 1) hn hhigh (by omega)
    simp only [hi, ↓reduceIte, List.cons_append, Hpack.Spec.intDecode, h1, h2, Nat.lt_irrefl]
    rw [← encodeRest_eq, loop_encodeRest]
    congr 2
    simp
    omega

theorem loop_cases (bs : List UInt8) (acc m i : Nat) (rest : List UInt8)
    (h : Hpack.Spec.intDecode.loop bs acc m = some (i, rest)) :
    (∃ j, decodeRest bs = some (j, rest) ∧ i = acc + j * 2 ^ m) ∨
    ∃ pre c, 128 ≤ c.toNat ∧ bs = pre ++ [c, 0] ++ rest := by
  induction bs generalizing acc m with
  | nil => simp [Hpack.Spec.intDecode.loop] at h
  | cons b bs ih =>
    have hb := toNat_lt b
    simp only [Hpack.Spec.intDecode.loop] at h
    split at h
    · rename_i hc
      rcases ih _ _ h with ⟨j', hj', hi⟩ | ⟨pre, c, hc', rfl⟩
      · by_cases hj0 : j' = 0
        · subst hj0
          right
          refine ⟨[], b, by omega, ?_⟩
          rw [decodeRest_iff] at hj'
          rw [hj', encodeRest]
          simp
        · left
          refine ⟨b.toNat - 128 + 128 * j', ?_, ?_⟩
          · rw [decodeRest_eq_rec]
            rw [decodeRest_eq_rec] at hj'
            simp [decodeRestRec, show ¬ b.toNat < 128 by omega, hj', hj0]
          · rw [hi, Nat.pow_add]
            have : (b.toNat - 128 + 128 * j') * 2 ^ m =
                (b.toNat % 128) * 2 ^ m + j' * (2 ^ m * 2 ^ 7) := by
              rw [show b.toNat % 128 = b.toNat - 128 by omega, Nat.add_mul]
              congr 1
              rw [Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128]
            rw [this]
            omega
      · right
        exact ⟨b :: pre, c, hc', by simp⟩
    · rename_i hc
      cases h
      left
      refine ⟨b.toNat, ?_, ?_⟩
      · rw [decodeRest_eq_rec]
        simp [decodeRestRec, show b.toNat < 128 by omega]
      · rw [Nat.mod_eq_of_lt (by omega)]

theorem decodeInt_of_rfc (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    Hpack.Spec.intDecode n b = some (i, rest) →
      decodeInt n b = some (i, rest) ∨
      ∃ pre c, pre ≠ [] ∧ 128 ≤ c.toNat ∧ b = pre ++ [c, 0] ++ rest := by
  intro h
  cases b with
  | nil => simp [Hpack.Spec.intDecode] at h
  | cons p bs =>
    simp only [Hpack.Spec.intDecode] at h
    split at h
    · rename_i hp
      cases h
      left
      simp [decodeInt_cons n hn, hp]
    · rename_i hp
      rcases loop_cases bs _ 0 i rest h with ⟨j, hj, hi⟩ | ⟨pre, c, hc, rfl⟩
      · left
        have hpos := pow_pos' n
        have : p.toNat % 2 ^ n = 2 ^ n - 1 := by
          have := Nat.mod_lt p.toNat hpos
          omega
        simp [decodeInt_cons n hn, hj, hi, this]
      · right
        exact ⟨p :: pre, c, by simp, hc, by simp⟩

end HpackProofs
