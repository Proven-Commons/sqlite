import Proofs.Bytes

/-!
  The varint reader against `Spec.Varint` and `Spec.varintValue`.
-/

namespace SqliteProofs

open Spec Sqlite

/-- The seven-bit digits of the bytes, after `acc`. -/
def f7 (acc : Nat) (bs : List UInt8) : Nat :=
  bs.foldl (fun n b => n * 128 + b.toNat % 128) acc

/-- What `go` does on bytes with the high bit set, then one more. -/
theorem go_run (pre : List UInt8) (x : UInt8) (rest : List UInt8) :
    ∀ acc i, (∀ y ∈ pre, 128 ≤ y.toNat) → i + pre.length ≤ 8 →
      readVarint.go acc i (pre ++ x :: rest) =
        if i + pre.length = 8 then some (f7 acc pre * 256 + x.toNat, 9, rest)
        else if x.toNat < 128 then some (f7 acc pre * 128 + x.toNat, i + pre.length + 1, rest)
        else readVarint.go (f7 acc pre * 128 + x.toNat % 128) (i + pre.length + 1) rest := by
  induction pre with
  | nil =>
    intro acc i _ _
    show readVarint.go acc i (x :: rest) = _
    rw [readVarint.go.eq_2]
    rfl
  | cons y pre ih =>
    intro acc i hpre hlen
    simp only [List.length_cons] at hlen
    have hy : 128 ≤ y.toNat := hpre y (by simp)
    rw [List.cons_append, readVarint.go.eq_2, ite_eq_right (by omega), ite_eq_right (by omega),
      ih _ _ (fun z hz => hpre z (by simp [hz])) (by omega)]
    have e1 : i + 1 + pre.length = i + (pre.length + 1) := by omega
    have e2 : f7 (acc * 128 + y.toNat % 128) pre = f7 acc (y :: pre) := rfl
    simp only [e1, e2, List.length_cons]

/-- What `go` gives back, it read from bytes with the high bit set, then
    one more. -/
theorem go_some (b : List UInt8) :
    ∀ acc i v k rest, i ≤ 8 → readVarint.go acc i b = some (v, k, rest) →
      ∃ pre x, b = pre ++ x :: rest ∧ (∀ y ∈ pre, 128 ≤ y.toNat) ∧ i + pre.length ≤ 8 ∧
        (i + pre.length = 8 ∧ v = f7 acc pre * 256 + x.toNat ∧ k = 9 ∨
         i + pre.length < 8 ∧ x.toNat < 128 ∧ v = f7 acc pre * 128 + x.toNat ∧
           k = i + pre.length + 1) := by
  induction b with
  | nil => intro acc i v k rest _ h; simp [readVarint.go] at h
  | cons y b ih =>
    intro acc i v k rest hi h
    rw [readVarint.go.eq_2] at h
    by_cases h8 : i = 8
    · rw [ite_eq_left h8] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], y, rfl, by simp, by simp [h8], Or.inl ⟨by simp [h8], by simp [f7], rfl⟩⟩
    · rw [ite_eq_right h8] at h
      by_cases hy : y.toNat < 128
      · rw [ite_eq_left hy] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨[], y, rfl, by simp, by simp; omega,
          Or.inr ⟨by simp; omega, hy, by simp [f7], by simp⟩⟩
      · rw [ite_eq_right hy] at h
        obtain ⟨pre, x, rfl, hpre, hlen, hcase⟩ := ih _ _ _ _ _ (by omega) h
        refine ⟨y :: pre, x, rfl, ?_, by simp; omega, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · omega
          · exact hpre z hz
        · simp only [List.length_cons, f7, List.foldl_cons]
          simp only [f7] at hcase
          rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
          · exact Or.inl ⟨by omega, h2, h3⟩
          · exact Or.inr ⟨by omega, h2, h3, by omega⟩

/-- A varint is bytes with the high bit set, then one more: the last of
    nine, or a byte with the high bit clear. -/
theorem varint_split (bs : List UInt8) :
    Varint bs ↔ ∃ pre x, bs = pre ++ [x] ∧ (∀ y ∈ pre, 128 ≤ y.toNat) ∧
      (pre.length = 8 ∨ pre.length < 8 ∧ x.toNat < 128) := by
  constructor
  · rintro ⟨h1, h9, hpre, hlast⟩
    obtain ⟨pre, x, hbs⟩ := List.eq_nil_or_concat bs |>.resolve_left (by
      intro h; subst h; simp at h1)
    rw [List.concat_eq_append] at hbs
    subst hbs
    refine ⟨pre, x, rfl, by simpa using hpre, ?_⟩
    simp only [List.length_append, List.length_singleton] at h9 hlast
    by_cases h : pre.length = 8
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hlast (by omega) x (by simp)⟩
  · rintro ⟨pre, x, rfl, hpre, hcase⟩
    refine ⟨by simp, by simp; omega, by simpa using hpre, ?_⟩
    intro hl y hy
    simp only [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hy
    subst hy
    simp only [List.length_append, List.length_singleton] at hl
    omega

theorem varintValue_split (pre : List UInt8) (x : UInt8)
    (hcase : pre.length = 8 ∨ pre.length < 8 ∧ x.toNat < 128) :
    varintValue (pre ++ [x]) =
      if pre.length = 8 then f7 0 pre * 256 + x.toNat else f7 0 pre * 128 + x.toNat := by
  unfold varintValue
  simp only [List.length_append, List.length_singleton]
  by_cases h : pre.length = 8
  · rw [ite_eq_left (by omega), ite_eq_left h, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
    simp [f7, List.getD_eq_getElem?_getD, h]
  · rw [ite_eq_right (by omega), ite_eq_right h]
    have hx : x.toNat < 128 := by omega
    simp [f7, List.foldl_append, Nat.mod_eq_of_lt hx]

theorem readVarint_iff (b : List UInt8) (v k : Nat) (rest : List UInt8) :
    Sqlite.readVarint b = some (v, k, rest) ↔
      ∃ bs, Varint bs ∧ varintValue bs = v ∧ bs.length = k ∧ b = bs ++ rest := by
  constructor
  · intro h
    obtain ⟨pre, x, rfl, hpre, hlen, hcase⟩ := go_some b 0 0 v k rest (by omega) h
    have hc : pre.length = 8 ∨ pre.length < 8 ∧ x.toNat < 128 := by omega
    refine ⟨pre ++ [x], (varint_split _).2 ⟨pre, x, rfl, hpre, hc⟩, ?_, ?_, by simp⟩
    · rw [varintValue_split pre x hc]
      rcases hcase with ⟨h1, h2, _⟩ | ⟨h1, _, h3, _⟩
      · rw [ite_eq_left (by omega), h2]
      · rw [ite_eq_right (by omega), h3]
    · simp only [List.length_append, List.length_singleton]
      omega
  · rintro ⟨bs, hv, rfl, rfl, rfl⟩
    obtain ⟨pre, x, rfl, hpre, hc⟩ := (varint_split _).1 hv
    show readVarint.go 0 0 _ = _
    rw [List.append_assoc, List.singleton_append,
      go_run pre x rest 0 0 hpre (by omega), varintValue_split pre x hc]
    simp only [Nat.zero_add, List.length_append, List.length_singleton]
    rcases hc with h | ⟨h, hx⟩
    · rw [ite_eq_left h, ite_eq_left h, h]
    · rw [ite_eq_right (by omega), ite_eq_left hx, ite_eq_right (by omega)]

end SqliteProofs
