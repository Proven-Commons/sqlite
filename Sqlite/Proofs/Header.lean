import Sqlite.Proofs.Bytes

/-!
  The header reader against `Sqlite.Spec.headerBytes` and `Sqlite.Spec.HeaderValid`.
-/

namespace SqliteProofs

open Sqlite.Spec Sqlite

theorem pageSizeOk_iff (n : Nat) :
    pageSizeOk n = true ↔ ∃ k, 9 ≤ k ∧ k ≤ 16 ∧ n = 2 ^ k := by
  constructor
  · intro h
    simp only [pageSizeOk, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨9, by decide⟩
    · exact ⟨10, by decide⟩
    · exact ⟨11, by decide⟩
    · exact ⟨12, by decide⟩
    · exact ⟨13, by decide⟩
    · exact ⟨14, by decide⟩
    · exact ⟨15, by decide⟩
    · exact ⟨16, by decide⟩
  · rintro ⟨k, h1, h2, rfl⟩
    have : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem guard_true : (guard True : Option Unit) = some () := rfl

theorem readBE_one' (a : UInt8) (l r : List UInt8) :
    readBE 1 ((a :: l) ++ r) = some (a.toNat, l ++ r) :=
  readBE_one a (l ++ r)

/-- The page size field gives back the page size. -/
theorem pageSize_code (ps : Nat) (h : ps < 65536) :
    (if (if ps = 1 then 65536 else ps) = 65536 then 1 else (if ps = 1 then 65536 else ps)) = ps := by
  by_cases h1 : ps = 1
  · simp [h1]
  · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem pageSize_code' (n : Nat) (h : ∃ k, 9 ≤ k ∧ k ≤ 16 ∧ n = 2 ^ k) :
    (if (if n = 65536 then 1 else n) = 1 then 65536 else (if n = 65536 then 1 else n)) = n := by
  obtain ⟨k, h1, h2, rfl⟩ := h
  have : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readHeader_some (file : List UInt8) (h : Header) (H : readHeader file = some h) :
    HeaderValid h ∧ ∃ rest, file = headerBytes h ++ rest := by
  unfold readHeader at H
  simp only [bind, Option.bind_eq_some_iff, Prod.exists, take?_eq, readBE_iff, guard_some,
    exists_and_left, exists_const, pure, Option.some.injEq, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, Nat.reducePow] at H
  obtain ⟨m, r, ⟨-, rfl⟩, rfl, ps, r, ⟨hps, rfl⟩, wv, r, ⟨hwv, rfl⟩, rv, r, ⟨hrv, rfl⟩,
    res, r, ⟨hres, rfl⟩, fr, r, ⟨-, rfl⟩, rfl,
    cc, r, ⟨hcc, rfl⟩, ds, r, ⟨hds, rfl⟩, ft, r, ⟨hft, rfl⟩, fc, r, ⟨hfc, rfl⟩,
    sc, r, ⟨hsc, rfl⟩, sf, r, ⟨hsf, rfl⟩, cs, r, ⟨hcs, rfl⟩, lr, r, ⟨hlr, rfl⟩,
    te, r, ⟨hte, rfl⟩, uv, r, ⟨huv, rfl⟩, iv, r, ⟨hiv, rfl⟩, ai, r, ⟨hai, rfl⟩,
    z, r, ⟨-, rfl⟩, rfl, vv, r, ⟨hvv, rfl⟩, sv, r, ⟨hsv, rfl⟩,
    ⟨⟨⟨⟨hok, hrv'⟩, hus⟩, hsf'⟩, hte'⟩, rfl⟩ := H
  refine ⟨?_, r, ?_⟩
  · simp only [HeaderValid, Nat.reducePow]
    exact ⟨(pageSizeOk_iff _).1 hok, hwv, hrv', hres, hus, hcc, hds, hft, hfc, hsc, hsf', hcs,
      hlr, by omega, huv, hiv, hai, hvv, hsv⟩
  · simp only [headerBytes, List.append_assoc, beBytes_one _ hwv, beBytes_one _ hrv,
      beBytes_one _ hres, pageSize_code ps hps, List.cons_append, List.nil_append]

theorem readHeader_bytes (h : Header) (hv : HeaderValid h) (rest : List UInt8) :
    readHeader (headerBytes h ++ rest) = some h := by
  have hv' := hv
  simp only [HeaderValid] at hv'
  obtain ⟨hps, hwv, hrv, hres, hus, hcc, hds, hft, hfc, hsc, hsf, hcs, hlr, hte, huv, hiv, hai,
    hvv, hsv⟩ := hv'
  have hps2 : (if h.pageSize = 65536 then 1 else h.pageSize) < 256 ^ 2 := by
    obtain ⟨k, h1, h2, h3⟩ := hps
    have : h.pageSize ≤ 65536 := by
      rw [h3]; exact Nat.pow_le_pow_right (by decide) h2
    split <;> simp only [Nat.reducePow] <;> omega
  have hrv1 : h.readVersion < 256 := by omega
  have hte' : ((h.textEncoding = 1 ∨ h.textEncoding = 2) ∨ h.textEncoding = 3) ∨
      h.textEncoding = 0 ∧ h.schemaFormat = 0 := by omega
  have b4 : ∀ n, n < 2 ^ 32 → n < 256 ^ 4 := fun n h => by simpa using h
  unfold readHeader headerBytes
  simp only [bind, List.append_assoc, take?_append' 16 magic _ rfl, Option.bind_some,
    readBE_append 2 _ _ hps2, readBE_one', take?_append' 3 [64, 32, 32] _ rfl,
    readBE_append 4 _ _ (b4 _ hcc), readBE_append 4 _ _ (b4 _ hds), readBE_append 4 _ _ (b4 _ hft),
    readBE_append 4 _ _ (b4 _ hfc), readBE_append 4 _ _ (b4 _ hsc),
    readBE_append 4 _ _ (b4 _ (by omega : h.schemaFormat < 2 ^ 32)),
    readBE_append 4 _ _ (b4 _ hcs), readBE_append 4 _ _ (b4 _ hlr),
    readBE_append 4 _ _ (b4 _ (by omega : h.textEncoding < 2 ^ 32)),
    readBE_append 4 _ _ (b4 _ huv), readBE_append 4 _ _ (b4 _ hiv), readBE_append 4 _ _ (b4 _ hai),
    take?_append' 20 (List.replicate 20 0) _ (by simp),
    readBE_append 4 _ _ (b4 _ hvv), readBE_append 4 _ _ (b4 _ hsv),
    toNat_toUInt8 _ hwv, toNat_toUInt8 _ hrv1, toNat_toUInt8 _ hres, pageSize_code' _ hps,
    (pageSizeOk_iff _).2 hps, guard_true, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, hrv, hus, hsf, hte', true_and, pure]

theorem readHeader_iff (file : List UInt8) (h : Header) :
    Sqlite.readHeader file = some h ↔ HeaderValid h ∧ ∃ rest, file = headerBytes h ++ rest := by
  constructor
  · exact readHeader_some file h
  · rintro ⟨hv, rest, rfl⟩
    exact readHeader_bytes h hv rest

end SqliteProofs
