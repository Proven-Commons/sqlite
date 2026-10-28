import Sqlite
import Spec.Defs
import Spec.Examples

/-!
  The statements a reviewer approves. Each `sorry` is proved under the
  same name in `Proofs/`, and `lake comparator` checks that each proof
  proves exactly the statement here.

  `Spec/Defs.lean` writes the file format down from "Database File
  Format" (https://www.sqlite.org/fileformat2.html). The code is in
  `Sqlite/Basic.lean`.
-/

namespace Spec

/-- The varint reader accepts exactly a varint of 1.6 at the start of
    its input, and gives its value, its length and what follows. -/
theorem readVarint_iff (b : List UInt8) (v k : Nat) (rest : List UInt8) :
    Sqlite.readVarint b = some (v, k, rest) ↔
      ∃ bs, Varint bs ∧ varintValue bs = v ∧ bs.length = k ∧ b = bs ++ rest := by
  sorry

/-- The header reader accepts exactly a file that starts with the 100
    bytes of a header this reader accepts, and gives that header. -/
theorem readHeader_iff (file : List UInt8) (h : Header) :
    Sqlite.readHeader file = some h ↔ HeaderValid h ∧ ∃ rest, file = headerBytes h ++ rest := by
  sorry

/-- The page reader gives a b-tree page exactly when the `n`th page is
    in the file and holds it, as `PageEncodes` says: the page header,
    the cell pointers, and each cell's bytes where its pointer says. -/
theorem readPage_iff (h : Header) (file : List UInt8) (n : Nat) (pg : Page) :
    Sqlite.readPage h file n = some pg ↔
      1 ≤ n ∧ n * h.pageSize ≤ file.length ∧ PageEncodes h n pg (pageOf h file n) := by
  sorry

/-- Nothing the page reader gives lies outside the file or its page:
    the page is in the file, and every cell starts after the cell pointer
    array and before the end of the usable size. -/
theorem readPage_inside (h : Header) (file : List UInt8) (n : Nat) (pg : Page)
    (hp : Sqlite.readPage h file n = some pg) :
    (n - 1) * h.pageSize + h.usable ≤ file.length ∧
    ∀ p ∈ pg.pointers,
      headerOffset n + pg.header.type.headerSize + 2 * pg.pointers.length ≤ p ∧ p < h.usable := by
  sorry

/-- The record reader accepts exactly a record of 2.1, and gives its
    values. -/
theorem readRecord_iff (p : List UInt8) (vs : List Value) :
    Sqlite.readRecord p = some vs ↔ RecordEncodes vs p := by
  sorry

/-- Worked by hand:
    - varints: 0, 127, 128 in two bytes, and nine bytes 0xFF, which is
      2^64 - 1 (1.6);
    - a payload of 10000 bytes on a table leaf page with a usable size of
      4096: X = 4061, M = 489, and K = 489 + 9511 mod 4092 = 1816, which
      is no more than X, so 1816 bytes stay on the page (1.6);
    - the record whose header is 03 01 13 (a header of 3 bytes, an 8-bit
      integer and a string of 3 bytes) and whose body is 07 61 62 63 is
      7 and "abc" (2.1);
    - the header SQLite wrote, in `sqliteHeaderBytes`, read field by
      field (1.3);
    - the page of `onePageFile`: a table leaf page with one cell, of
      rowid 1, whose record is the integer 5 (1.6, 2.1). -/
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
  sorry

/-- Inputs the readers refuse, each for a rule:
    - a varint that ends before its last byte (1.6);
    - headers with the header string zeroed, a page size of 768, a read
      version of 3, a usable size of 479, a text encoding of 0, and a
      maximum embedded payload fraction of 63 (1.3);
    - page 2 of a one-page file, and page 0 (1.2);
    - serial type 10, which "will never appear in a well-formed database
      file", a body one byte longer than its columns, a header size
      larger than the record, and a header with no column (2.1). -/
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
  sorry

end Spec
