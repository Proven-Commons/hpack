/-
  Integers with an N-bit prefix (RFC 7541, section 5.1).
-/

import Spec.Defs
import Hpack

namespace HpackProofs

open Hpack

theorem toNat_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt b

theorem toNat_toUInt8 {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp; omega

theorem toUInt8_toNat (b : UInt8) : b.toNat.toUInt8 = b := by simp

/-! ### The octets after the prefix -/

theorem encodeRest_eq (j : Nat) : encodeRest j = (Spec.intOctets.rest j).map Nat.toUInt8 := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [encodeRest, Spec.intOctets.rest]
    by_cases h : j < 128
    · simp [h, show ¬ j ≥ 128 by omega]
    · simp [h, show j ≥ 128 by omega, ih (j / 128) (by omega)]

theorem decodeRest_encodeRest (j : Nat) (rest : List UInt8) :
    decodeRest (encodeRest j ++ rest) = some (j, rest) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rw [encodeRest]
    by_cases h : j < 128
    · simp only [h, ↓reduceIte, List.singleton_append, decodeRest, toNat_toUInt8 (by omega : j < 256)]
    · simp only [h, ↓reduceIte, List.cons_append, decodeRest,
        toNat_toUInt8 (by omega : j % 128 + 128 < 256)]
      rw [ih (j / 128) (by omega)]
      simp only [show ¬ (j % 128 + 128 < 128) by omega, ↓reduceIte,
        show ¬ (j / 128 = 0) by omega]
      congr 2
      omega

theorem eq_of_decodeRest {bs : List UInt8} {j : Nat} {rest : List UInt8}
    (h : decodeRest bs = some (j, rest)) : bs = encodeRest j ++ rest := by
  induction bs generalizing j with
  | nil => simp [decodeRest] at h
  | cons b bs ih =>
    simp only [decodeRest] at h
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

/-! ### The statements -/

theorem encodeInt_eq (n high i : Nat) (_hn : 1 ≤ n ∧ n ≤ 8) (hhigh : high < 2 ^ (8 - n)) :
    encodeInt n high i = Spec.intEncode n high i := by
  have hmod : high % 2 ^ (8 - n) = high := Nat.mod_eq_of_lt hhigh
  unfold encodeInt Spec.intEncode Spec.intOctets
  rw [hmod]
  by_cases h : i < 2 ^ n - 1
  · simp [h]
  · simp [h, encodeRest_eq]

theorem decodeInt_iff (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (hn : 1 ≤ n ∧ n ≤ 8) :
    decodeInt n b = some (i, rest) ↔
      ∃ high, high < 2 ^ (8 - n) ∧ b = Spec.intEncode n high i ++ rest := by
  have hpos := pow_pos' n
  constructor
  · intro h
    cases b with
    | nil => simp [decodeInt] at h
    | cons p bs =>
      obtain ⟨hhigh, hsplit⟩ := octet_split n hn p
      refine ⟨p.toNat / 2 ^ n, hhigh, ?_⟩
      rw [← encodeInt_eq n _ i hn hhigh]
      simp only [decodeInt] at h
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
      simp only [h, ↓reduceIte, List.singleton_append, decodeInt, h1, h2]
    · obtain ⟨h1, h2, _⟩ := first_toNat n high (2 ^ n - 1) hn hhigh (by omega)
      simp only [h, ↓reduceIte, List.cons_append, decodeInt, h1, h2, Nat.lt_irrefl,
        decodeRest_encodeRest]
      congr 2
      omega

/-! ### Against the decoding pseudocode -/

theorem loop_encodeRest (j : Nat) (rest : List UInt8) (acc m : Nat) :
    Spec.intDecode.loop (encodeRest j ++ rest) acc m = some (acc + j * 2 ^ m, rest) := by
  induction j using Nat.strongRecOn generalizing acc m with
  | ind j ih =>
    rw [encodeRest]
    by_cases h : j < 128
    · simp only [h, ↓reduceIte, List.singleton_append, Spec.intDecode.loop,
        toNat_toUInt8 (by omega : j < 256)]
      simp [show j / 128 = 0 by omega, Nat.mod_eq_of_lt h]
    · simp only [h, ↓reduceIte, List.cons_append, Spec.intDecode.loop,
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
    decodeInt n b = some (i, rest) → Spec.intDecode n b = some (i, rest) := by
  intro h
  obtain ⟨high, hhigh, rfl⟩ := (decodeInt_iff n b i rest hn).mp h
  have hpos := pow_pos' n
  unfold Spec.intEncode Spec.intOctets
  by_cases hi : i < 2 ^ n - 1
  · obtain ⟨h1, h2, _⟩ := first_toNat n high i hn hhigh (by omega)
    simp only [hi, ↓reduceIte, List.map_nil, List.singleton_append, Spec.intDecode, h1, h2]
  · obtain ⟨h1, h2, _⟩ := first_toNat n high (2 ^ n - 1) hn hhigh (by omega)
    simp only [hi, ↓reduceIte, List.cons_append, Spec.intDecode, h1, h2, Nat.lt_irrefl]
    rw [← encodeRest_eq, loop_encodeRest]
    congr 2
    simp
    omega

theorem loop_cases (bs : List UInt8) (acc m i : Nat) (rest : List UInt8)
    (h : Spec.intDecode.loop bs acc m = some (i, rest)) :
    (∃ j, decodeRest bs = some (j, rest) ∧ i = acc + j * 2 ^ m) ∨
    ∃ pre c, 128 ≤ c.toNat ∧ bs = pre ++ [c, 0] ++ rest := by
  induction bs generalizing acc m with
  | nil => simp [Spec.intDecode.loop] at h
  | cons b bs ih =>
    have hb := toNat_lt b
    simp only [Spec.intDecode.loop] at h
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
          · simp [decodeRest, show ¬ b.toNat < 128 by omega, hj', hj0]
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
      · simp [decodeRest, show b.toNat < 128 by omega]
      · rw [Nat.mod_eq_of_lt (by omega)]

theorem decodeInt_of_rfc (n : Nat) (b : List UInt8) (i : Nat) (rest : List UInt8)
    (_hn : 1 ≤ n ∧ n ≤ 8) :
    Spec.intDecode n b = some (i, rest) →
      decodeInt n b = some (i, rest) ∨
      ∃ pre c, pre ≠ [] ∧ 128 ≤ c.toNat ∧ b = pre ++ [c, 0] ++ rest := by
  intro h
  cases b with
  | nil => simp [Spec.intDecode] at h
  | cons p bs =>
    simp only [Spec.intDecode] at h
    split at h
    · rename_i hp
      cases h
      left
      simp [decodeInt, hp]
    · rename_i hp
      rcases loop_cases bs _ 0 i rest h with ⟨j, hj, hi⟩ | ⟨pre, c, hc, rfl⟩
      · left
        have hpos := pow_pos' n
        have : p.toNat % 2 ^ n = 2 ^ n - 1 := by
          have := Nat.mod_lt p.toNat hpos
          omega
        simp [decodeInt, hj, hi, this]
      · right
        exact ⟨p :: pre, c, by simp, hc, by simp⟩

end HpackProofs
