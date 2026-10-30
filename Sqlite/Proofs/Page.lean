import Sqlite.Proofs.Varint
import Sqlite.Proofs.Header
import Sqlite.Proofs.Record

/-!
  The page reader against `Sqlite.Spec.PageEncodes`: the page header, the cell
  pointers, payloads, cells, and the page.
-/

namespace SqliteProofs

open Sqlite.Spec Sqlite

theorem pageType?_eq (n : Nat) (t : PageType) : pageType? n = some t ↔ t.code = n := by
  constructor
  · intro h
    unfold pageType? at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  · rintro rfl
    cases t <;> rfl

theorem code_lt (t : PageType) : t.code < 256 := by cases t <;> decide

theorem contentStart_code (cs : Nat) (h : cs < 65536) :
    (if cs = 0 then 65536 else cs) % 65536 = cs := by
  by_cases h0 : cs = 0
  · simp [h0]
  · rw [ite_eq_right h0, Nat.mod_eq_of_lt h]

theorem contentStart_code' (cs : Nat) (h1 : 1 ≤ cs) (h2 : cs ≤ 65536) :
    (if cs % 65536 = 0 then 65536 else cs % 65536) = cs := by
  by_cases h : cs = 65536
  · subst h; rfl
  · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega)]

theorem readPageHeader_some (b : List UInt8) (ph : PageHeader) (r : List UInt8)
    (H : readPageHeader b = some (ph, r)) : PageHeaderValid ph ∧ b = pageHeaderBytes ph ++ r := by
  unfold readPageHeader at H
  simp only [bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, pageType?_eq,
    Nat.reducePow] at H
  obtain ⟨fl, r1, ⟨hfl, rfl⟩, ty, rfl, ff, r2, ⟨hff, rfl⟩, cc, r3, ⟨hcc, rfl⟩,
    cs, r4, ⟨hcs, rfl⟩, fr, r5, ⟨hfr, rfl⟩, H⟩ := H
  split at H
  · rename_i hi
    simp only [Option.bind_eq_some_iff, Prod.exists, readBE_iff, Nat.reducePow, pure,
      Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨p, r6, ⟨hp, rfl⟩, rfl, rfl⟩ := H
    refine ⟨⟨hff, hcc, by dsimp only; split <;> omega, by dsimp only; split <;> omega, hfr, hi, hp⟩, ?_⟩
    simp only [pageHeaderBytes, beBytes_one _ (code_lt ty), beBytes_one _ hfr,
      contentStart_code _ hcs, List.append_assoc, List.cons_append, List.nil_append]
  · rename_i hi
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl⟩ := H
    refine ⟨⟨hff, hcc, by dsimp only; split <;> omega, by dsimp only; split <;> omega, hfr, by simpa using hi⟩, ?_⟩
    simp only [pageHeaderBytes, beBytes_one _ (code_lt ty), beBytes_one _ hfr,
      contentStart_code _ hcs, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil]

theorem readPageHeader_bytes (ph : PageHeader) (hv : PageHeaderValid ph) (r : List UInt8) :
    readPageHeader (pageHeaderBytes ph ++ r) = some (ph, r) := by
  obtain ⟨ty, ff, cc, cs, fr, rm⟩ := ph
  obtain ⟨hff, hcc, hcs1, hcs2, hfr, hrm⟩ := hv
  dsimp only at hff hcc hcs1 hcs2 hfr hrm
  have hff' : ff < 256 ^ 2 := by simpa using hff
  have hcc' : cc < 256 ^ 2 := by simpa using hcc
  have hcs' : cs % 65536 < 256 ^ 2 := by simp only [Nat.reducePow]; omega
  unfold readPageHeader pageHeaderBytes
  cases rm with
  | some p =>
    obtain ⟨hi, hp⟩ := hrm
    have hp' : p < 256 ^ 4 := by simpa using hp
    simp only [List.append_assoc, List.cons_append, List.nil_append, readBE_one, bind,
      Option.bind_some,
      toNat_toUInt8 _ (code_lt ty), (pageType?_eq _ ty).2 rfl, readBE_append 2 _ _ hff',
      readBE_append 2 _ _ hcc', readBE_append 2 _ _ hcs', toNat_toUInt8 _ hfr,
      contentStart_code' _ hcs1 hcs2, hi, ite_true, readBE_append 4 _ _ hp', pure]
  | none =>
    have hi : ty.interior = false := hrm
    simp only [List.append_assoc, List.cons_append, List.nil_append, readBE_one, bind,
      Option.bind_some,
      toNat_toUInt8 _ (code_lt ty), (pageType?_eq _ ty).2 rfl, readBE_append 2 _ _ hff',
      readBE_append 2 _ _ hcc', readBE_append 2 _ _ hcs', toNat_toUInt8 _ hfr,
      contentStart_code' _ hcs1 hcs2, hi, pure]
    rfl

theorem readPageHeader_iff (b : List UInt8) (ph : PageHeader) (r : List UInt8) :
    readPageHeader b = some (ph, r) ↔ PageHeaderValid ph ∧ b = pageHeaderBytes ph ++ r := by
  constructor
  · exact readPageHeader_some b ph r
  · rintro ⟨hv, rfl⟩
    exact readPageHeader_bytes ph hv r

theorem readPointers_iff (k : Nat) :
    ∀ b ps, readPointers k b = some ps ↔
      ps.length = k ∧ (∀ p ∈ ps, p < 2 ^ 16) ∧ ∃ rest, b = pointerBytes ps ++ rest := by
  induction k with
  | zero =>
    intro b ps
    simp only [readPointers, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, by simp, b, by simp [pointerBytes]⟩
    · rintro ⟨h, -, -⟩; exact (List.eq_nil_of_length_eq_zero h).symm
  | succ k ih =>
    intro b ps
    rw [readPointers.eq_2]
    constructor
    · intro h
      simp only [bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, ih, pure,
        Option.some.injEq] at h
      obtain ⟨p, r, ⟨hp, rfl⟩, ps', ⟨hl, hb, rest, rfl⟩, rfl⟩ := h
      refine ⟨by simp [hl], ?_, rest, by simp [pointerBytes]⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨by simpa using hp, hb⟩
    · rintro ⟨hl, hb, rest, rfl⟩
      cases ps with
      | nil => simp at hl
      | cons p ps =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [List.mem_cons, forall_eq_or_imp] at hb
        have hp : p < 256 ^ 2 := by simpa using hb.1
        have := (ih (pointerBytes ps ++ rest) ps).2 ⟨hl, hb.2, rest, rfl⟩
        simp only [pointerBytes, List.flatMap_cons, List.append_assoc] at this ⊢
        simp only [readBE_append 2 _ _ hp, bind, Option.bind_some, this, pure]

theorem localOf_eq (t : PageType) (U P : Nat) : localOf t U P = localSize t U P := by
  cases t <;> rfl

theorem int64_eq (n : Nat) : int64 n = toInt64 n := by
  simp only [int64, toInt64, Nat.reducePow, Int.reducePow]

theorem readPayload_iff (t : PageType) (U P : Nat) (b kept : List UInt8) (ovf : Option Nat)
    (k : Nat) :
    readPayload t U P b = some (kept, ovf, k) ↔
      ∃ bs rest, PayloadEncodes t U P kept ovf bs ∧ k = bs.length ∧ b = bs ++ rest := by
  unfold readPayload
  simp only [localOf_eq]
  constructor
  · intro H
    simp only [bind, Option.bind_eq_some_iff, Prod.exists, take?_eq] at H
    obtain ⟨loc, r, ⟨hl, rfl⟩, H⟩ := H
    split at H
    · rename_i hlt
      simp only [Option.bind_eq_some_iff, Prod.exists, readBE_iff, pure, Option.some.injEq,
        Prod.mk.injEq] at H
      obtain ⟨o, r', ⟨ho, rfl⟩, rfl, rfl, rfl⟩ := H
      refine ⟨loc ++ beBytes 4 o, r', ⟨hl, ?_⟩, by simp [beBytes_length, hl], by simp⟩
      rw [ite_eq_left hlt]
      exact ⟨o, by simpa using ho, rfl, rfl⟩
    · rename_i hlt
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨rfl, rfl, rfl⟩ := H
      refine ⟨loc, r, ⟨hl, ?_⟩, hl.symm, rfl⟩
      rw [ite_eq_right hlt]
      exact ⟨rfl, rfl⟩
  · rintro ⟨bs, rest, ⟨hl, hif⟩, rfl, rfl⟩
    by_cases hlt : localSize t U P < P
    · rw [ite_eq_left hlt] at hif
      obtain ⟨o, ho, rfl, rfl⟩ := hif
      have ho' : o < 256 ^ 4 := by simpa using ho
      simp only [List.append_assoc, bind, take?_append' _ kept _ hl, Option.bind_some, hlt,
        ite_true, readBE_append 4 o rest ho', pure, List.length_append, beBytes_length, hl]
    · rw [ite_eq_right hlt] at hif
      obtain ⟨rfl, rfl⟩ := hif
      simp only [bind, take?_append' _ bs _ hl, Option.bind_some, hlt, ite_false, pure, hl]

theorem readCell_iff (t : PageType) (U : Nat) (b : List UInt8) (c : Cell) (size : Nat) :
    readCell t U b = some (c, size) ↔
      ∃ bs rest, CellEncodes t U c bs ∧ size = bs.length ∧ b = bs ++ rest := by
  cases t with
  | tableLeaf =>
    constructor
    · intro H
      simp only [readCell, bind, Option.bind_eq_some_iff, Prod.exists, readVarint_iff,
        readPayload_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨P, n1, r1, ⟨vp, hvp, rfl, rfl, rfl⟩, rowid, n2, r2, ⟨vr, hvr, rfl, rfl, rfl⟩,
        loc, ovf, n3, ⟨pb, rest, hpe, rfl, rfl⟩, rfl, rfl⟩ := H
      refine ⟨vp ++ vr ++ pb, rest, ?_, by simp [Nat.add_assoc], by simp⟩
      unfold CellEncodes
      exact ⟨vp, vr, pb, hvp, hvr, rfl, rfl, rfl, by simp [int64_eq], hpe⟩
    · rintro ⟨bs, rest, hc, rfl, rfl⟩
      simp only [CellEncodes] at hc
      obtain ⟨vp, vr, pb, hvp, hvr, rfl, h1, h2, h3, hpe⟩ := hc
      have hp := (readPayload_iff _ _ _ _ _ _ _).2 ⟨pb, rest, hpe, rfl, rfl⟩
      simp only [readCell, List.append_assoc, readVarint_append _ _ hvp, readVarint_append _ _ hvr,
        bind, Option.bind_some, hp, pure, Option.some.injEq, Prod.mk.injEq, List.length_append]
      refine ⟨?_, by omega⟩
      cases c
      simp_all [int64_eq]
  | tableInterior =>
    constructor
    · intro H
      simp only [readCell, bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, readVarint_iff,
        pure, Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨k, r1, ⟨hk, rfl⟩, rowid, n2, r2, ⟨vr, hvr, rfl, rfl, rfl⟩, rfl, rfl⟩ := H
      refine ⟨beBytes 4 k ++ vr, r2, ?_, by simp [beBytes_length], by simp⟩
      unfold CellEncodes
      exact ⟨k, vr, by simpa using hk, hvr, rfl, by simp [int64_eq]⟩
    · rintro ⟨bs, rest, hc, rfl, rfl⟩
      simp only [CellEncodes] at hc
      obtain ⟨k, vr, hk, hvr, rfl, rfl⟩ := hc
      have hk' : k < 256 ^ 4 := by simpa using hk
      simp only [readCell, List.append_assoc, readBE_append 4 k _ hk', readVarint_append _ _ hvr,
        bind, Option.bind_some, pure, int64_eq, List.length_append, beBytes_length]
  | indexLeaf =>
    constructor
    · intro H
      simp only [readCell, bind, Option.bind_eq_some_iff, Prod.exists, readVarint_iff,
        readPayload_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨P, n1, r1, ⟨vp, hvp, rfl, rfl, rfl⟩, loc, ovf, n3, ⟨pb, rest, hpe, rfl, rfl⟩,
        rfl, rfl⟩ := H
      refine ⟨vp ++ pb, rest, ?_, by simp, by simp⟩
      unfold CellEncodes
      exact ⟨vp, pb, hvp, rfl, rfl, rfl, rfl, hpe⟩
    · rintro ⟨bs, rest, hc, rfl, rfl⟩
      simp only [CellEncodes] at hc
      obtain ⟨vp, pb, hvp, rfl, h1, h2, h3, hpe⟩ := hc
      have hp := (readPayload_iff _ _ _ _ _ _ _).2 ⟨pb, rest, hpe, rfl, rfl⟩
      simp only [readCell, List.append_assoc, readVarint_append _ _ hvp,
        bind, Option.bind_some, hp, pure, Option.some.injEq, Prod.mk.injEq, List.length_append]
      refine ⟨?_, by simp⟩
      cases c
      simp_all
  | indexInterior =>
    constructor
    · intro H
      simp only [readCell, bind, Option.bind_eq_some_iff, Prod.exists, readBE_iff, readVarint_iff,
        readPayload_iff, pure, Option.some.injEq, Prod.mk.injEq] at H
      obtain ⟨k, r0, ⟨hk, rfl⟩, P, n1, r1, ⟨vp, hvp, rfl, rfl, rfl⟩, loc, ovf, n3,
        ⟨pb, rest, hpe, rfl, rfl⟩, rfl, rfl⟩ := H
      refine ⟨beBytes 4 k ++ vp ++ pb, rest, ?_, by simp [beBytes_length, Nat.add_assoc],
        by simp⟩
      unfold CellEncodes
      exact ⟨k, vp, pb, by simpa using hk, hvp, rfl, rfl, rfl, rfl, hpe⟩
    · rintro ⟨bs, rest, hc, rfl, rfl⟩
      simp only [CellEncodes] at hc
      obtain ⟨k, vp, pb, hk, hvp, rfl, h1, h2, h3, hpe⟩ := hc
      have hk' : k < 256 ^ 4 := by simpa using hk
      have hp := (readPayload_iff _ _ _ _ _ _ _).2 ⟨pb, rest, hpe, rfl, rfl⟩
      simp only [readCell, List.append_assoc, readBE_append 4 k _ hk', readVarint_append _ _ hvp,
        bind, Option.bind_some, hp, pure, Option.some.injEq, Prod.mk.injEq, List.length_append,
        beBytes_length]
      refine ⟨?_, by omega⟩
      cases c
      simp_all

/-- What `readCells` checks of each cell, as `PageEncodes` says it. -/
def CellsAt (t : PageType) (U start : Nat) (page : List UInt8) (ptrs : List Nat)
    (cells : List Cell) : Prop :=
  cells.length = ptrs.length ∧ ∀ pc ∈ ptrs.zip cells, ∃ bs,
    CellEncodes t U pc.2 bs ∧ start ≤ pc.1 ∧ pc.1 + bs.length ≤ U ∧
    (page.drop pc.1).take bs.length = bs

theorem readCells_iff (t : PageType) (U start : Nat) (page : List UInt8) (ptrs : List Nat) :
    ∀ cells, readCells t U start page ptrs = some cells ↔ CellsAt t U start page ptrs cells := by
  induction ptrs with
  | nil =>
    intro cells
    simp only [readCells, Option.some.injEq, CellsAt, List.length_nil, List.zip_nil_left,
      List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · rintro rfl; rfl
    · intro h; exact (List.eq_nil_of_length_eq_zero h).symm
  | cons p ps ih =>
    intro cells
    rw [readCells.eq_2]
    constructor
    · intro H
      simp only [bind, Option.bind_eq_some_iff, Prod.exists, guard_some, exists_const,
        readCell_iff, ih, pure, Option.some.injEq] at H
      obtain ⟨hs, c, size, ⟨bs, rest, hc, rfl, hd⟩, hU, cs, ⟨hl, hall⟩, rfl⟩ := H
      refine ⟨by simp [hl], ?_⟩
      intro pc hpc
      simp only [List.zip_cons_cons, List.mem_cons] at hpc
      rcases hpc with rfl | hpc
      · exact ⟨bs, hc, hs, hU, by rw [hd]; exact List.take_left⟩
      · exact hall pc hpc
    · rintro ⟨hl, hall⟩
      cases cells with
      | nil => simp at hl
      | cons c cs =>
        obtain ⟨bs, hc, hs, hU, ht⟩ := hall (p, c) (by simp)
        have hd : page.drop p = bs ++ (page.drop p).drop bs.length := by
          conv => lhs; rw [← List.take_append_drop bs.length (page.drop p)]
          rw [ht]
        have h1 := (readCell_iff t U (page.drop p) c bs.length).2 ⟨bs, _, hc, rfl, hd⟩
        have h2 := (ih cs).2 ⟨by simpa using hl, fun pc h => hall pc (by simp [h])⟩
        simp only [bind, guard_of _ hs, Option.bind_some, h1, guard_of _ hU, h2, pure]

theorem pageHeaderBytes_length (ph : PageHeader) (hv : PageHeaderValid ph) :
    (pageHeaderBytes ph).length = ph.type.headerSize := by
  obtain ⟨-, -, -, -, -, hrm⟩ := hv
  unfold pageHeaderBytes PageType.headerSize
  cases h : ph.rightmost with
  | some p =>
    rw [h] at hrm
    simp [beBytes_length, hrm.1]
  | none =>
    rw [h] at hrm
    simp [beBytes_length, hrm]

theorem pointerBytes_length (ps : List Nat) : (pointerBytes ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pointerBytes, List.flatMap_cons, List.length_append, beBytes_length] at ih ⊢
    rw [ih, List.length_cons]
    omega

theorem page_length (file : List UInt8) (n ps : Nat) (hn : 1 ≤ n) :
    ((file.drop ((n - 1) * ps)).take ps).length = ps ↔ n * ps ≤ file.length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, List.length_take, List.length_drop, Nat.succ_mul]
  rcases Nat.eq_zero_or_pos ps with rfl | hps
  · simp
  · omega

theorem readPage_iff (h : Header) (file : List UInt8) (n : Nat) (pg : Page) :
    Sqlite.readPage h file n = some pg ↔
      1 ≤ n ∧ n * h.pageSize ≤ file.length ∧ PageEncodes h n pg (pageOf h file n) := by
  constructor
  · intro H
    unfold readPage at H
    simp only [bind, Option.bind_eq_some_iff, Prod.exists, guard_some, exists_const,
      readPageHeader_iff, readPointers_iff, readCells_iff, Bool.and_eq_true, decide_eq_true_eq,
      pure, Option.some.injEq] at H
    obtain ⟨hn, hlen, ph, r, ⟨hv, hd⟩, ptrs, ⟨hpl, hpb, rest, rfl⟩, ⟨hc1, hc2⟩, cells,
      ⟨hcl, hcells⟩, rfl⟩ := H
    refine ⟨hn, (page_length _ _ _ hn).1 hlen, hv, hpl.symm, hcl, hpb, ?_, ?_, hc2, hcells⟩
    rotate_left
    · show headerOffset n + ph.type.headerSize + 2 * ptrs.length ≤ ph.contentStart
      unfold headerOffset PageType.headerSize
      rw [hpl]
      exact hc1
    show List.take _ (List.drop (headerOffset n) (pageOf h file n)) = _
    unfold headerOffset pageOf
    rw [hd, ← List.append_assoc]
    apply List.take_left'
    simp [pageHeaderBytes_length _ hv, pointerBytes_length, PageType.headerSize]
  · rintro ⟨hn, hlen, hv, hpl, hcl, hpb, ht, hc1, hc2, hcells⟩
    unfold readPage
    have hlen' := (page_length file n h.pageSize hn).2 hlen
    have hd : (pageOf h file n).drop (headerOffset n) = pageHeaderBytes pg.header ++
        (pointerBytes pg.pointers ++
          ((pageOf h file n).drop (headerOffset n)).drop
            (pg.header.type.headerSize + 2 * pg.pointers.length)) := by
      rw [← List.append_assoc, ← ht, List.take_append_drop]
    unfold pageOf headerOffset at hd
    generalize List.drop (pg.header.type.headerSize + 2 * pg.pointers.length) _ = R at hd
    have h1 := (readPageHeader_iff _ _ _).2 ⟨hv, hd⟩
    have h2 := (readPointers_iff pg.header.cellCount (pointerBytes pg.pointers ++ R) pg.pointers).2
      ⟨hpl.symm, hpb, R, rfl⟩
    have h3 := (readCells_iff pg.header.type (h.pageSize - h.reserved) pg.header.contentStart
      ((file.drop ((n - 1) * h.pageSize)).take h.pageSize) pg.pointers pg.cells).2 ⟨hcl, hcells⟩
    have hc1' : (if n = 1 then 100 else 0) + (if pg.header.type.interior = true then 12 else 8) +
        2 * pg.header.cellCount ≤ pg.header.contentStart := by
      rw [hpl]; exact hc1
    simp only [bind, guard_of _ hn, Option.bind_some, guard_of _ hlen', h1, h2, h3, pure,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [guard_of _ ⟨hc1', hc2⟩, Option.bind_some]

theorem cellEncodes_length (t : PageType) (U : Nat) (c : Cell) (bs : List UInt8)
    (h : CellEncodes t U c bs) : 1 ≤ bs.length := by
  cases t <;> unfold CellEncodes at h
  · obtain ⟨k, vp, rest, -, -, rfl, -⟩ := h
    simp only [List.length_append, beBytes_length]
    omega
  · obtain ⟨k, vr, -, -, rfl, -⟩ := h
    simp only [List.length_append, beBytes_length]
    omega
  · obtain ⟨vp, rest, hv, rfl, -⟩ := h
    have := hv.1
    simp only [List.length_append]
    omega
  · obtain ⟨vp, vr, rest, hv, -, rfl, -⟩ := h
    have := hv.1
    simp only [List.length_append]
    omega

theorem mem_zip_left {α β} (as : List α) (bs : List β) (a : α) (ha : a ∈ as)
    (hl : bs.length = as.length) : ∃ b, (a, b) ∈ as.zip bs := by
  induction as generalizing bs with
  | nil => simp at ha
  | cons x as ih =>
    cases bs with
    | nil => simp at hl
    | cons y bs =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨y, by simp⟩
      · obtain ⟨b, hb⟩ := ih bs ha (by simpa using hl)
        exact ⟨b, by simp [hb]⟩

theorem readPage_inside (h : Header) (file : List UInt8) (n : Nat) (pg : Page)
    (hp : Sqlite.readPage h file n = some pg) :
    (n - 1) * h.pageSize + h.usable ≤ file.length ∧
    ∀ p ∈ pg.pointers,
      headerOffset n + pg.header.type.headerSize + 2 * pg.pointers.length ≤ p ∧ p < h.usable := by
  obtain ⟨hn, hlen, -, -, hcl, -, -, hc1, -, hcells⟩ := (readPage_iff h file n pg).1 hp
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Header.usable]
    rw [Nat.succ_mul] at hlen
    omega
  · intro p hmem
    obtain ⟨c, hc⟩ := mem_zip_left _ _ p hmem hcl
    obtain ⟨bs, hce, hs, hU, -⟩ := hcells (p, c) hc
    have := cellEncodes_length _ _ _ _ hce
    exact ⟨by omega, by omega⟩

end SqliteProofs
