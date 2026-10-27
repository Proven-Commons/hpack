/-
  The Huffman code (RFC 7541, section 5.2 and Appendix B).

  The facts about the 257 codes are checked by the kernel, by
  evaluation: the codes agree with the "code as bits" column of the
  specification, no code is a prefix of another, and no code is all
  ones and shorter than 8 bits. The rest is proved for every input.
-/

import Spec.Defs
import Hpack

namespace HpackProofs

open Hpack

set_option maxRecDepth 100000

/-! ### Facts about the table, checked by evaluation -/

/-- The code's table, from the "code as hex" column, is the
    specification's, from the "code as bits" column. -/
theorem table_eq_b : (huffmanTable == Spec.huffmanCodes) = true := by decide +kernel

theorem table_eq : huffmanTable = Spec.huffmanCodes := beq_iff_eq.mp table_eq_b

theorem table_length : huffmanTable.length = 257 := by decide +kernel

/-- Each code fits in its length. -/
def bounded : Bool := huffmanTable.all fun (x, l) => x < 2 ^ l

theorem bounded_eq : bounded = true := by decide +kernel

/-- No code is a prefix of another: for two different symbols, the
    longer code does not start with the shorter. -/
def prefixFreeN : Bool :=
  huffmanTable.zipIdx.all fun ((x1, l1), i) => huffmanTable.zipIdx.all fun ((x2, l2), j) =>
    i == j || !(l1 ≤ l2 && x2 / 2 ^ (l2 - l1) == x1)

theorem prefixFreeN_eq : prefixFreeN = true := by decide +kernel

/-- EOS is 30 ones. -/
theorem eos_eq : huffmanTable[256]? = some (2 ^ 30 - 1, 30) := by decide +kernel

/-! ### Bits of a number -/

theorem toBits_succ (x l : Nat) : toBits x (l + 1) = (x / 2 ^ l % 2 == 1) :: toBits x l := by
  simp [toBits, List.range_succ]

theorem toBits_length (x l : Nat) : (toBits x l).length = l := by
  simp [toBits]

theorem toBits_getElem (x l k : Nat) (hk : k < (toBits x l).length) :
    (toBits x l)[k] = (x / 2 ^ (l - 1 - k) % 2 == 1) := by
  simp only [toBits, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]

theorem toBits_take (x l1 l2 : Nat) (h : l1 ≤ l2) :
    (toBits x l2).take l1 = toBits (x / 2 ^ (l2 - l1)) l1 := by
  apply List.ext_getElem
  · simp [toBits_length]; omega
  · intro k hk1 hk2
    rw [List.getElem_take, toBits_getElem, toBits_getElem]
    simp only [toBits_length, List.length_take] at hk1 hk2
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 4
    omega

theorem toBits_mod (x y l : Nat) (h : toBits x l = toBits y l) : x % 2 ^ l = y % 2 ^ l := by
  induction l with
  | zero => simp [Nat.mod_one]
  | succ l ih =>
    rw [toBits_succ, toBits_succ, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih h2]
    have hx := Nat.mod_lt (x / 2 ^ l) (by decide : 0 < 2)
    have hy := Nat.mod_lt (y / 2 ^ l) (by decide : 0 < 2)
    have : x / 2 ^ l % 2 = y / 2 ^ l % 2 := by
      revert h1
      cases hxv : x / 2 ^ l % 2 <;> cases hyv : y / 2 ^ l % 2 <;> simp_all <;> omega
    rw [this]

theorem toBits_prefix {x1 l1 x2 l2 : Nat} (h1 : x1 < 2 ^ l1) (h2 : x2 < 2 ^ l2)
    (hp : toBits x1 l1 <+: toBits x2 l2) : l1 ≤ l2 ∧ x2 / 2 ^ (l2 - l1) = x1 := by
  have hl := hp.length_le
  simp only [toBits_length] at hl
  refine ⟨hl, ?_⟩
  rw [List.prefix_iff_eq_take, toBits_length, toBits_take x2 l1 l2 hl] at hp
  have := toBits_mod _ _ _ hp
  have hlt : x2 / 2 ^ (l2 - l1) < 2 ^ l1 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rw [show l1 + (l2 - l1) = l2 by omega]
    exact h2
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hlt] at this
  exact this.symm

/-! ### What the facts give -/

theorem codes_length : codes.length = 257 := by
  simp [codes, table_length]

theorem codes_getElem (i : Nat) (hi : i < codes.length) :
    ∃ hi' : i < huffmanTable.length,
      codes[i]'hi = toBits huffmanTable[i].1 huffmanTable[i].2 ∧
      huffmanTable[i].1 < 2 ^ huffmanTable[i].2 := by
  have hi' : i < huffmanTable.length := by simpa [codes] using hi
  refine ⟨hi', by simp [codes], ?_⟩
  have h := bounded_eq
  unfold bounded at h
  rw [List.all_eq_true] at h
  simpa using h _ (List.getElem_mem hi')

theorem codes_eq : codes = (List.range 257).map Spec.code := by
  apply List.ext_getElem
  · simp [codes_length]
  · intro i h1 h2
    obtain ⟨hi', hc, -⟩ := codes_getElem i h1
    simp only [hc, List.getElem_map, List.getElem_range, Spec.code, ← table_eq,
      List.getElem?_eq_getElem hi']
    rfl

theorem mem_zipIdx_self {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (l[i], i) ∈ l.zipIdx := by
  have h' : i < l.zipIdx.length := by simp [h]
  have := List.getElem_mem h'
  rw [List.getElem_zipIdx] at this
  simpa using this

theorem prefix_free {i j : Nat} (hi : i < codes.length) (hj : j < codes.length) (hij : i ≠ j) :
    ¬ codes[i] <+: codes[j] := by
  obtain ⟨hi', hci, hbi⟩ := codes_getElem i hi
  obtain ⟨hj', hcj, hbj⟩ := codes_getElem j hj
  intro hp
  simp only [hci, hcj] at hp
  obtain ⟨hl, hx⟩ := toBits_prefix hbi hbj hp
  have h := prefixFreeN_eq
  unfold prefixFreeN at h
  rw [List.all_eq_true] at h
  have h2 := h _ (mem_zipIdx_self huffmanTable i hi')
  rw [List.all_eq_true] at h2
  have h3 := h2 _ (mem_zipIdx_self huffmanTable j hj')
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_imp, decide_eq_true_eq] at h3
  rcases h3 with h3 | h3
  · exact hij h3
  · exact absurd hx (by simpa using h3 hl)

theorem lookup_indexed (l : List (List Bool)) (k : Nat) (bits : List Bool) :
    ((indexed l k).filter (·.1.length == bits.length)).lookup bits =
      (l.findIdx? (· == bits)).map (· + k) := by
  induction l generalizing k with
  | nil => rfl
  | cons c cs ih =>
    rw [indexed, List.filter_cons, List.findIdx?_cons]
    by_cases hc : c = bits
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte, Option.map_some, Nat.zero_add]
      rw [List.lookup_cons]
      simp
    · have h1 : (c == bits) = false := by simpa using hc
      have h2 : (bits == c) = false := by
        cases h : bits == c
        · rfl
        · exact absurd (beq_iff_eq.mp h).symm hc
      rw [h1]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map]
      have e : ((· + k) ∘ (· + 1)) = (· + (k + 1)) := by funext x; simp only [Function.comp_apply]; omega
      rw [e, ← ih (k + 1)]
      split
      · rw [List.lookup_cons, h2]
      · rfl

theorem codes_short : ∀ c ∈ codes, c.length ≤ 30 := by
  intro c hc
  unfold codes at hc
  obtain ⟨⟨x, l⟩, hm, rfl⟩ := List.mem_map.mp hc
  rw [toBits_length]
  have : ∀ p ∈ huffmanTable, p.2 ≤ 30 := by decide +kernel
  exact this _ hm

theorem symbolOf_eq (bits : List Bool) : symbolOf bits = codes.findIdx? (· == bits) := by
  unfold symbolOf codesByLength
  rw [Array.getElem?_map, Array.getElem?_range]
  by_cases h : bits.length < 31
  · simp only [h, ↓reduceIte, Option.map_some, Option.getD_some]
    rw [lookup_indexed]
    simp
  · simp only [h, ↓reduceIte, Option.map_none, Option.getD_none]
    rw [show List.lookup bits ([] : List (List Bool × Nat)) = none from rfl, eq_comm]
    rw [List.findIdx?_eq_none_iff]
    intro c hc
    have := codes_short c hc
    cases he : c == bits
    · rfl
    · rw [beq_iff_eq.mp he] at this
      omega

theorem symbolOf_self {i : Nat} (hi : i < codes.length) : symbolOf codes[i] = some i := by
  rw [symbolOf_eq]
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by simp, fun j hji => ?_⟩
  simp only [beq_iff_eq]
  intro he
  have hj : j < codes.length := Nat.lt_trans hji hi
  have hne : j ≠ i := Nat.ne_of_lt hji
  apply prefix_free hj hi hne
  rw [he]
  exact List.prefix_refl _

theorem symbolOf_some {bits : List Bool} {s : Nat} (h : symbolOf bits = some s) :
    ∃ hs : s < codes.length, codes[s] = bits := by
  rw [symbolOf_eq, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hs, heq, _⟩ := h
  exact ⟨hs, by simpa using heq⟩

theorem codes_eos : ∃ h : 256 < codes.length, codes[256]'h = List.replicate 30 true := by
  have h : 256 < codes.length := by rw [codes_length]; omega
  refine ⟨h, ?_⟩
  obtain ⟨hi', hc, -⟩ := codes_getElem 256 h
  simp only [hc]
  have he := eos_eq
  rw [List.getElem?_eq_getElem hi'] at he
  simp only [Option.some.injEq] at he
  rw [he]
  decide +kernel

theorem symbolOf_ones {j : Nat} (hj : j < 8) : symbolOf (List.replicate j true) = none := by
  cases hs : symbolOf (List.replicate j true) with
  | none => rfl
  | some s =>
    exfalso
    obtain ⟨hsl, hcs⟩ := symbolOf_some hs
    obtain ⟨he, hce⟩ := codes_eos
    by_cases h256 : s = 256
    · subst h256
      have := congrArg List.length (hcs.symm.trans hce)
      simp at this
      omega
    · apply prefix_free hsl he h256
      rw [hcs, hce]
      exact ⟨List.replicate (30 - j) true, by rw [List.replicate_append_replicate]; congr 1; omega⟩

theorem symbolBits_eq (c : UInt8) : symbolBits c = Spec.code c.toNat := by
  have hc := UInt8.toNat_lt c
  unfold symbolBits
  rw [codes_eq, List.getD_eq_getElem?_getD]
  simp only [List.getElem?_map, List.getElem?_range (show c.toNat < 257 by omega),
    Option.map_some, Option.getD_some]

theorem symbolBits_getElem (c : UInt8) :
    ∃ h : c.toNat < codes.length, symbolBits c = codes[c.toNat] := by
  have hc := UInt8.toNat_lt c
  have h : c.toNat < codes.length := by rw [codes_length]; omega
  refine ⟨h, ?_⟩
  unfold symbolBits
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ### Octets and bits -/

theorem toBits_octet (b : UInt8) : toBits b.toNat 8 = Spec.octetBits b := rfl

theorem octetBits_byte : ∀ b7 b6 b5 b4 b3 b2 b1 b0 : Bool,
    Spec.octetBits ([b7, b6, b5, b4, b3, b2, b1, b0].foldl
      (fun acc (b : Bool) => 2 * acc + if b then 1 else 0) 0).toUInt8 =
      [b7, b6, b5, b4, b3, b2, b1, b0] := by
  intro b7 b6 b5 b4 b3 b2 b1 b0
  cases b7 <;> cases b6 <;> cases b5 <;> cases b4 <;> cases b3 <;> cases b2 <;> cases b1 <;>
    cases b0 <;> decide +kernel

theorem bits_ofBits (l : List Bool) (h : l.length % 8 = 0) : Spec.bits (ofBits l) = l := by
  induction l using ofBits.induct with
  | case1 b7 b6 b5 b4 b3 b2 b1 b0 rest ih =>
    rw [ofBits]
    simp only [Spec.bits, List.flatMap_cons] at ih ⊢
    rw [octetBits_byte, ih (by simp at h; omega)]
    rfl
  | case2 l hl =>
    match l, hl, h with
    | [], _, _ => simp [ofBits, Spec.bits]
    | [_], _, h => simp at h
    | [_, _], _, h => simp at h
    | [_, _, _], _, h => simp at h
    | [_, _, _, _], _, h => simp at h
    | [_, _, _, _, _], _, h => simp at h
    | [_, _, _, _, _, _], _, h => simp at h
    | [_, _, _, _, _, _, _], _, h => simp at h
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hl, _ => exact absurd rfl (hl _ _ _ _ _ _ _ _ _)

theorem ofBits_octetBits_all :
    ∀ n, n < 256 → ofBits (Spec.octetBits n.toUInt8) = [n.toUInt8] := by
  decide +kernel

theorem ofBits_octetBits (a : UInt8) : ofBits (Spec.octetBits a) = [a] := by
  have := ofBits_octetBits_all a.toNat (UInt8.toNat_lt a)
  simpa using this

theorem ofBits_append (l rest : List Bool) (hl : l.length = 8) :
    ofBits (l ++ rest) = ofBits l ++ ofBits rest := by
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => simp [ofBits]

theorem ofBits_bits (d : List UInt8) : ofBits (Spec.bits d) = d := by
  induction d with
  | nil => simp [Spec.bits, ofBits]
  | cons a d ih =>
    simp only [Spec.bits, List.flatMap_cons] at ih ⊢
    rw [ofBits_append _ _ (by simp [Spec.octetBits]), ofBits_octetBits, ih]
    rfl

theorem bits_length (d : List UInt8) : (Spec.bits d).length = 8 * d.length := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    simp only [Spec.bits, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]
    simp [Spec.octetBits]
    omega

theorem bits_inj {d e : List UInt8} (h : Spec.bits d = Spec.bits e) : d = e := by
  rw [← ofBits_bits d, ← ofBits_bits e, h]

/-! ### Decoding -/

/-- The concatenated codes of a string. -/
def codesOf (s : List UInt8) : List Bool := s.flatMap fun c => Spec.code c.toNat

theorem flatMap_symbolBits (s : List UInt8) : s.flatMap symbolBits = codesOf s := by
  unfold codesOf
  congr 1
  funext c
  exact symbolBits_eq c

theorem decodeBits_sound (bits pending : List Bool) (s : List UInt8)
    (h : decodeBits bits pending = some s) :
    ∃ k, k < 8 ∧ pending ++ bits = codesOf s ++ List.replicate k true := by
  induction bits generalizing pending s with
  | nil =>
    simp only [decodeBits] at h
    split at h
    · rename_i hp
      cases h
      refine ⟨pending.length, hp.1, ?_⟩
      simp only [List.append_nil, codesOf, List.flatMap_nil, List.nil_append]
      rw [List.eq_replicate_iff]
      refine ⟨rfl, fun b hb => ?_⟩
      have := hp.2
      rw [List.all_eq_true] at this
      simpa using this b hb
    · contradiction
  | cons b bs ih =>
    simp only [decodeBits] at h
    split at h
    · rename_i sym hsym
      split at h
      · contradiction
      · rename_i h256
        split at h
        · rename_i out hout
          cases h
          obtain ⟨k, hk, hbs⟩ := ih [] out hout
          obtain ⟨hs, hcode⟩ := symbolOf_some hsym
          refine ⟨k, hk, ?_⟩
          have hs' : sym < 256 := by rw [codes_length] at hs; omega
          have hsb : symbolBits sym.toUInt8 = codes[sym] := by
            obtain ⟨h1, h2⟩ := symbolBits_getElem sym.toUInt8
            rw [h2]
            congr 1
            simp
            omega
          simp only [List.nil_append] at hbs
          have hc : codesOf (sym.toUInt8 :: out) = (pending ++ [b]) ++ codesOf out := by
            simp only [codesOf, List.flatMap_cons]
            rw [← symbolBits_eq, hsb, hcode]
          rw [hc, hbs]
          simp
        · contradiction
    · rename_i hnone
      split at h
      · obtain ⟨k, hk, h'⟩ := ih _ s h
        exact ⟨k, hk, by simpa using h'⟩
      · exact absurd h (Option.some_ne_none _).symm

theorem decodeBits_ones (i j : Nat) (h : i + j < 8) :
    decodeBits (List.replicate j true) (List.replicate i true) = some [] := by
  induction j generalizing i with
  | zero => simp [decodeBits, show i < 8 by omega]
  | succ j ih =>
    rw [List.replicate_succ]
    simp only [decodeBits]
    rw [show List.replicate i true ++ [true] = List.replicate (i + 1) true by
      rw [List.replicate_succ']]
    rw [symbolOf_ones (by omega)]
    simp only [List.length_replicate, show i + 1 < 30 by omega, ↓reduceIte]
    exact ih (i + 1) (by omega)

/-- Reading the rest of a code, after its first bits. -/
theorem decodeBits_code {c : Nat} (hc : c < 256) (p q tail : List Bool)
    (hpq : p ++ q = codes[c]'(by rw [codes_length]; omega)) (hq : q ≠ []) :
    decodeBits (q ++ tail) p = (decodeBits tail []).map (c.toUInt8 :: ·) := by
  have hcl : c < codes.length := by rw [codes_length]; omega
  induction q generalizing p with
  | nil => contradiction
  | cons b q ih =>
    rw [List.cons_append]
    simp only [decodeBits]
    by_cases hq' : q = []
    · subst hq'
      rw [hpq, symbolOf_self hcl]
      simp only [show c ≠ 256 by omega, ↓reduceIte, List.nil_append]
      cases decodeBits tail [] <;> rfl
    · have hnone : symbolOf (p ++ [b]) = none := by
        cases hs : symbolOf (p ++ [b]) with
        | none => rfl
        | some s =>
          exfalso
          obtain ⟨hsl, hcs⟩ := symbolOf_some hs
          have hpre : codes[s] <+: codes[c] := by
            rw [hcs, ← hpq]
            exact ⟨q, by simp⟩
          by_cases hsc : s = c
          · subst hsc
            have h1 := congrArg List.length hcs
            have h2 := congrArg List.length hpq
            simp at h1 h2
            have hql : 0 < q.length := List.length_pos_iff.mpr hq'
            omega
          · exact prefix_free hsl hcl hsc hpre
      have hlen : (p ++ [b]).length < 30 := by
        have h1 := congrArg List.length hpq
        have h2 := codes_short _ (List.getElem_mem hcl)
        have hql : 0 < q.length := List.length_pos_iff.mpr hq'
        simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
        omega
      rw [hnone]
      simp only [hlen, ↓reduceIte]
      exact ih (p ++ [b]) (by simpa using hpq) hq'

theorem decodeBits_complete (s : List UInt8) (k : Nat) (hk : k < 8) :
    decodeBits (codesOf s ++ List.replicate k true) [] = some s := by
  induction s with
  | nil => simpa [codesOf] using decodeBits_ones 0 k (by omega)
  | cons c s ih =>
    have hc := UInt8.toNat_lt c
    obtain ⟨hcl, hcb⟩ := symbolBits_getElem c
    simp only [codesOf, List.flatMap_cons, List.append_assoc]
    rw [← symbolBits_eq, hcb]
    have hne : codes[c.toNat] ≠ [] := by
      intro he
      have hj : (if c.toNat = 0 then 1 else 0) < codes.length := by
        rw [codes_length]; split <;> omega
      apply prefix_free hcl hj (by split <;> omega)
      rw [he]
      exact List.nil_prefix
    rw [decodeBits_code (c := c.toNat) (by omega) [] _ _ (by simp) hne]
    rw [← codesOf, ih]
    simp

/-! ### The statements -/

theorem huffmanDecode_bits (d : List UInt8) :
    huffmanDecode d = decodeBits (Spec.bits d) [] := rfl

theorem huffmanEncode_spec (s : List UInt8) : Spec.HuffmanEncodes s (huffmanEncode s) := by
  refine ⟨(8 - (codesOf s).length % 8) % 8, by omega, ?_⟩
  unfold huffmanEncode
  rw [flatMap_symbolBits, bits_ofBits]
  · rfl
  · simp only [List.length_append, List.length_replicate]
    omega

theorem huffmanDecode_iff (d s : List UInt8) :
    huffmanDecode d = some s ↔ Spec.HuffmanEncodes s d := by
  rw [huffmanDecode_bits]
  constructor
  · intro h
    obtain ⟨k, hk, h'⟩ := decodeBits_sound _ _ _ h
    exact ⟨k, hk, by simpa [codesOf] using h'⟩
  · rintro ⟨k, hk, h⟩
    rw [h]
    exact decodeBits_complete s k hk

theorem huffmanDecode_encode (s : List UInt8) : huffmanDecode (huffmanEncode s) = some s :=
  (huffmanDecode_iff _ _).mpr (huffmanEncode_spec s)

theorem huffmanEncodes_unique {s d e : List UInt8} (hd : Spec.HuffmanEncodes s d)
    (he : Spec.HuffmanEncodes s e) : d = e := by
  obtain ⟨k, hk, hd⟩ := hd
  obtain ⟨k', hk', he⟩ := he
  have ld := congrArg List.length hd
  have le := congrArg List.length he
  simp only [bits_length, List.length_append, List.length_replicate] at ld le
  have : k = k' := by omega
  subst this
  exact bits_inj (hd.trans he.symm)

theorem huffmanEncode_decode (d s : List UInt8) :
    huffmanDecode d = some s → huffmanEncode s = d := by
  intro h
  exact huffmanEncodes_unique (huffmanEncode_spec s) ((huffmanDecode_iff d s).mp h)

end HpackProofs
