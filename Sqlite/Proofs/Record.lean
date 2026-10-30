import Sqlite.Proofs.Varint
import Sqlite.Proofs.Header

/-!
  The record reader against `Sqlite.Spec.RecordEncodes`.
-/

namespace SqliteProofs

open Sqlite.Spec Sqlite

theorem guard_of (p : Prop) [Decidable p] (hp : p) : (guard p : Option Unit) = some () :=
  (guard_some p ()).mpr hp

theorem varint_ne_nil (bs : List UInt8) (h : Varint bs) : bs ≠ [] := by
  intro e; subst e; exact absurd h.1 (by simp)

theorem readVarint_append (bs rest : List UInt8) (h : Varint bs) :
    readVarint (bs ++ rest) = some (varintValue bs, bs.length, rest) :=
  (readVarint_iff _ _ _ _).2 ⟨bs, h, rfl, rfl, rfl⟩

theorem small (t : Nat) (h : t < 12) :
    t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 := by
  omega

theorem sizeOf_eq (t : Nat) : Sqlite.sizeOf t = contentSize t := by
  rcases Nat.lt_or_ge t 12 with h | h
  · rcases small t h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 12 := ⟨t - 12, by omega⟩
    show _ = some (if (n + 12) % 2 = 0 then (n + 12 - 12) / 2 else (n + 12 - 13) / 2)
    unfold Sqlite.sizeOf
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), Option.some.injEq]
    split <;> omega

theorem signed_eq (c : List UInt8) (h : 1 ≤ c.length) : signed c = signedOf c := by
  have e1 : (256 : Nat) ^ c.length = 2 ^ (8 * c.length) := by rw [Nat.pow_mul]
  have e2 : 2 ^ (8 * c.length) = 2 * 2 ^ (8 * c.length - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have e3 : (256 : Int) ^ c.length = 2 ^ (8 * c.length) := by rw [Int.pow_mul]; rfl
  unfold signed signedOf
  simp only [bigEndian_eq, e3]
  by_cases hc : beNat c < 2 ^ (8 * c.length - 1)
  · rw [ite_eq_left (by omega), ite_eq_left hc]
  · rw [ite_eq_right (by omega), ite_eq_right hc]

theorem columnValue_eq (t : Nat) (c : List UInt8) (h : Sqlite.sizeOf t = some c.length) :
    columnValue t c = valueOf t c := by
  rcases Nat.lt_or_ge t 12 with ht | ht
  · rcases small t ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Sqlite.sizeOf] at h <;> simp [columnValue, valueOf, bigEndian_eq] <;> rw [signed_eq _ (by omega)]
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 12 := ⟨t - 12, by omega⟩
    show _ = if (n + 12) % 2 = 0 then Value.blob c else Value.text c
    unfold columnValue
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The columns, by the values of their serial types. -/
def ColsN : List Nat → List (List UInt8) → List Value → Prop
  | [], [], [] => True
  | n :: ns, c :: cs, v :: vs => contentSize n = some c.length ∧ v = valueOf n c ∧ ColsN ns cs vs
  | _, _, _ => False

theorem colsN_length (ns : List Nat) :
    ∀ cs vs, ColsN ns cs vs → vs.length = ns.length := by
  induction ns with
  | nil => intro cs vs h; cases cs <;> cases vs <;> simp_all [ColsN]
  | cons n ns ih =>
    intro cs vs h
    cases cs <;> cases vs <;> simp only [ColsN] at h
    simp [ih _ _ h.2.2]

theorem columnsEncode_iff (ts : List (List UInt8)) :
    ∀ cs vs, ColumnsEncode ts cs vs ↔ (∀ t ∈ ts, Varint t) ∧ ColsN (ts.map varintValue) cs vs := by
  induction ts with
  | nil => intro cs vs; cases cs <;> cases vs <;> simp [ColumnsEncode, ColsN]
  | cons t ts ih =>
    intro cs vs
    cases cs <;> cases vs <;> simp only [ColumnsEncode, ColsN, List.map_cons, and_false]
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h4⟩, h2, h3, h5⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩

theorem readColumns_iff (ns : List Nat) :
    ∀ body vs, readColumns ns body = some vs ↔ ∃ cs, body = cs.flatten ∧ ColsN ns cs vs := by
  induction ns with
  | nil =>
    intro body vs
    constructor
    · intro h
      cases body with
      | nil =>
        rw [readColumns.eq_1, Option.some.injEq] at h
        exact ⟨[], rfl, by subst h; trivial⟩
      | cons x xs => rw [readColumns.eq_2] at h; exact absurd h (by simp)
    · rintro ⟨cs, rfl, hc⟩
      cases cs <;> cases vs <;> simp_all [ColsN, readColumns.eq_1]
  | cons n ns ih =>
    intro body vs
    rw [readColumns.eq_3]
    constructor
    · intro h
      simp only [bind, Option.bind_eq_some_iff, Prod.exists, take?_eq, ih, pure,
        Option.some.injEq] at h
      obtain ⟨size, hsize, c, r, ⟨hcl, rfl⟩, vs', ⟨cs, rfl, hcs⟩, rfl⟩ := h
      rw [← hcl] at hsize
      refine ⟨c :: cs, rfl, ?_, ?_, hcs⟩
      · rw [← sizeOf_eq]; exact hsize
      · exact columnValue_eq _ _ hsize
    · rintro ⟨cs, rfl, hc⟩
      cases cs with
      | nil => cases vs <;> simp [ColsN] at hc
      | cons c cs =>
        cases vs with
        | nil => simp [ColsN] at hc
        | cons v vs =>
          obtain ⟨h1, rfl, h3⟩ := hc
          have hs : Sqlite.sizeOf n = some c.length := by rw [sizeOf_eq]; exact h1
          have hr := (ih cs.flatten vs).2 ⟨cs, rfl, h3⟩
          simp only [List.flatten_cons, hs, bind, Option.bind_some,
            take?_append' _ c _ rfl, hr, pure, columnValue_eq _ _ hs]

theorem readTypes_some (fuel : Nat) :
    ∀ b ns, readTypes fuel b = some ns →
      ∃ ts : List (List UInt8), (∀ t ∈ ts, Varint t) ∧ b = ts.flatten ∧
        ns = ts.map varintValue := by
  induction fuel with
  | zero =>
    intro b ns h
    cases b with
    | nil => rw [readTypes.eq_1, Option.some.injEq] at h; exact ⟨[], by simp, rfl, h.symm⟩
    | cons x xs => rw [readTypes.eq_2] at h; exact absurd h (by simp)
  | succ f ih =>
    intro b ns h
    cases b with
    | nil => rw [readTypes.eq_1, Option.some.injEq] at h; exact ⟨[], by simp, rfl, h.symm⟩
    | cons x xs =>
      rw [readTypes.eq_3 _ _ (by simp)] at h
      simp only [bind, Option.bind_eq_some_iff, Prod.exists, pure, Option.some.injEq] at h
      obtain ⟨t, k, r, hv, ts', hts, rfl⟩ := h
      obtain ⟨bs, hbs, rfl, rfl, he⟩ := (readVarint_iff _ _ _ _).1 hv
      obtain ⟨ts, htv, rfl, rfl⟩ := ih _ _ hts
      refine ⟨bs :: ts, ?_, by simp [he], rfl⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hbs, htv⟩

theorem readTypes_flatten (ts : List (List UInt8)) :
    ∀ fuel, (∀ t ∈ ts, Varint t) → ts.flatten.length ≤ fuel →
      readTypes fuel ts.flatten = some (ts.map varintValue) := by
  induction ts with
  | nil => intro fuel _ _; exact readTypes.eq_1 _
  | cons t ts ih =>
    intro fuel hv hl
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    have hne := varint_ne_nil t hv.1
    have h1 := hv.1.1
    simp only [List.flatten_cons, List.length_append] at hl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [List.flatten_cons, readTypes.eq_3 _ _ (by simp [hne]), readVarint_append _ _ hv.1]
    simp only [bind, Option.bind_some, ih f hv.2 (by omega), pure, List.map_cons]

theorem readRecord_iff (p : List UInt8) (vs : List Value) :
    Sqlite.readRecord p = some vs ↔ RecordEncodes vs p := by
  constructor
  · intro H
    unfold readRecord at H
    simp only [bind, Option.bind_eq_some_iff, Prod.exists, guard_some, take?_eq,
      exists_and_left, exists_const] at H
    obtain ⟨hsize, n, r, hv, hle, hdr, body, ⟨hl, rfl⟩, ns, hts, hne, hcols⟩ := H
    obtain ⟨hs, hvar, rfl, rfl, rfl⟩ := (readVarint_iff _ _ _ _).1 hv
    obtain ⟨ts, htv, rfl, rfl⟩ := readTypes_some _ _ _ hts
    obtain ⟨cs, rfl, hc⟩ := (readColumns_iff _ _ _).1 hcols
    refine ⟨?_, hs, ts, cs, hvar, by omega, (columnsEncode_iff _ _ _).2 ⟨htv, hc⟩, by simp⟩
    intro e
    have := colsN_length _ _ _ hc
    rw [e] at this
    exact hne (List.eq_nil_of_length_eq_zero this.symm)
  · intro H
    obtain ⟨hne, hs, ts, cs, hvar, hval, hcols, rfl⟩ := H
    obtain ⟨htv, hc⟩ := (columnsEncode_iff _ _ _).1 hcols
    have h4 : ts.map varintValue ≠ [] := by
      intro e
      have := colsN_length _ _ _ hc
      rw [e] at this
      exact hne (List.eq_nil_of_length_eq_zero this)
    unfold readRecord
    simp only [List.append_assoc, readVarint_append _ _ hvar, bind, Option.bind_some,
      guard_of _ (by omega : hs.length ≤ varintValue hs),
      take?_append' (varintValue hs - hs.length) ts.flatten cs.flatten (by omega),
      readTypes_flatten ts _ htv (Nat.le_refl _), guard_of _ h4,
      (readColumns_iff _ _ _).2 ⟨cs, rfl, hc⟩]

end SqliteProofs
