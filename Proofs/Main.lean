/-
  The statements of `Spec.lean`, each proved from the lemmas in the
  other files of `Proofs/`. `lake comparator` checks that each theorem
  here is exactly the one in `Spec.lean`.
-/

import Proofs.Page
import Spec.Examples

namespace Spec

theorem readVarint_iff (b : List UInt8) (v k : Nat) (rest : List UInt8) :
    Sqlite.readVarint b = some (v, k, rest) ↔
      ∃ bs, Varint bs ∧ varintValue bs = v ∧ bs.length = k ∧ b = bs ++ rest :=
  SqliteProofs.readVarint_iff b v k rest

theorem readHeader_iff (file : List UInt8) (h : Header) :
    Sqlite.readHeader file = some h ↔ HeaderValid h ∧ ∃ rest, file = headerBytes h ++ rest :=
  SqliteProofs.readHeader_iff file h

theorem readPage_iff (h : Header) (file : List UInt8) (n : Nat) (pg : Page) :
    Sqlite.readPage h file n = some pg ↔
      1 ≤ n ∧ n * h.pageSize ≤ file.length ∧ PageEncodes h n pg (pageOf h file n) :=
  SqliteProofs.readPage_iff h file n pg

theorem readPage_inside (h : Header) (file : List UInt8) (n : Nat) (pg : Page)
    (hp : Sqlite.readPage h file n = some pg) :
    (n - 1) * h.pageSize + h.usable ≤ file.length ∧
    ∀ p ∈ pg.pointers,
      headerOffset n + pg.header.type.headerSize + 2 * pg.pointers.length ≤ p ∧ p < h.usable :=
  SqliteProofs.readPage_inside h file n pg hp

theorem readRecord_iff (p : List UInt8) (vs : List Value) :
    Sqlite.readRecord p = some vs ↔ RecordEncodes vs p :=
  SqliteProofs.readRecord_iff p vs

theorem examples :
    Sqlite.readVarint [0x00] = some (0, 1, []) ∧
    Sqlite.readVarint [0x7F, 0x55] = some (127, 1, [0x55]) ∧
    Sqlite.readVarint [0x81, 0x00] = some (128, 2, []) ∧
    Sqlite.readVarint (List.replicate 9 0xFF) = some (2 ^ 64 - 1, 9, []) ∧
    Sqlite.localOf .tableLeaf 4096 10000 = 1816 ∧
    Sqlite.readRecord [0x03, 0x01, 0x13, 0x07, 0x61, 0x62, 0x63] =
      some [.int 7, .text [0x61, 0x62, 0x63]] ∧
    Sqlite.readHeader sqliteHeaderBytes = some sqliteHeader ∧
    Sqlite.readPage sqliteHeader onePageFile 1 =
      some { header := { type := .tableLeaf, firstFreeblock := 0, cellCount := 1,
                         contentStart := 507, fragmented := 0, rightmost := none },
             pointers := [507],
             cells := [{ leftChild := none, payloadSize := some 3, rowid := some 1,
                         payload := [0x02, 0x01, 0x05], overflow := none }] } ∧
    Sqlite.readRecord [0x02, 0x01, 0x05] = some [.int 5] := by
  decide +kernel

theorem rejects :
    Sqlite.readVarint [0x81, 0x80] = none ∧
    Sqlite.readHeader (List.replicate 16 0 ++ sqliteHeaderBytes.drop 16) = none ∧
    Sqlite.readHeader (headerBytes { sqliteHeader with pageSize := 768 }) = none ∧
    Sqlite.readHeader (headerBytes { sqliteHeader with readVersion := 3 }) = none ∧
    Sqlite.readHeader (headerBytes { sqliteHeader with reserved := 33 }) = none ∧
    Sqlite.readHeader (headerBytes { sqliteHeader with textEncoding := 0 }) = none ∧
    Sqlite.readHeader (sqliteHeaderBytes.set 21 63) = none ∧
    Sqlite.readPage sqliteHeader onePageFile 2 = none ∧
    Sqlite.readPage sqliteHeader onePageFile 0 = none ∧
    Sqlite.readRecord [0x02, 0x0A] = none ∧
    Sqlite.readRecord [0x02, 0x01, 0x07, 0x00] = none ∧
    Sqlite.readRecord [0x05, 0x01] = none ∧
    Sqlite.readRecord [0x01] = none := by
  decide +kernel

end Spec
