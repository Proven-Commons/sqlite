/-
  Reading the SQLite database file format: the database header, one
  b-tree page with its cells, and records. The structures the reader
  gives back are those of `Spec/Defs.lean`, and so is the header string;
  the functions here are the code under proof, and share nothing else
  with the specification.
-/

import Spec.Defs

namespace Sqlite

open Spec (Header PageType PageHeader Cell Page Value)

/-- Splits off the first `w` bytes, if there are that many. Measures
    only those `w`. -/
def take? (w : Nat) (b : List UInt8) : Option (List UInt8 × List UInt8) :=
  let c := b.take w
  if c.length = w then some (c, b.drop w) else none

/-- The bytes as a big-endian unsigned integer. -/
def bigEndian (bs : List UInt8) : Nat :=
  bs.foldl (fun n b => n * 256 + b.toNat) 0

/-- A `w`-byte big-endian integer at the start of the input, and the
    rest. -/
def readBE (w : Nat) (b : List UInt8) : Option (Nat × List UInt8) :=
  (take? w b).map fun (c, r) => (bigEndian c, r)

/-- A varint at the start of the input (1.6): its value, how many bytes
    it takes, and the rest. Each of the first eight bytes gives its low
    seven bits and ends the varint when its high bit is clear; a ninth
    byte gives all eight. -/
def readVarint (b : List UInt8) : Option (Nat × Nat × List UInt8) :=
  go 0 0 b
where
  go (acc i : Nat) : List UInt8 → Option (Nat × Nat × List UInt8)
    | [] => none
    | x :: rest =>
      if i = 8 then some (acc * 256 + x.toNat, 9, rest)
      else if x.toNat < 128 then some (acc * 128 + x.toNat, i + 1, rest)
      else go (acc * 128 + x.toNat % 128) (i + 1) rest

/-! ## The database header -/

/-- Whether a page size is a power of two from 512 to 65536. -/
def pageSizeOk (n : Nat) : Bool :=
  [512, 1024, 2048, 4096, 8192, 16384, 32768, 65536].contains n

/-- The database header at the start of a file (1.3), or `none` when
    the file does not start with one this reader accepts. -/
def readHeader (file : List UInt8) : Option Header := do
  let (m, r) ← take? 16 file
  guard (m = Spec.magic)
  let (ps, r) ← readBE 2 r
  let pageSize := if ps = 1 then 65536 else ps
  let (wv, r) ← readBE 1 r
  let (rv, r) ← readBE 1 r
  let (res, r) ← readBE 1 r
  let (fr, r) ← take? 3 r
  guard (fr = [64, 32, 32])
  let (changeCounter, r) ← readBE 4 r
  let (databaseSize, r) ← readBE 4 r
  let (freelistTrunk, r) ← readBE 4 r
  let (freelistCount, r) ← readBE 4 r
  let (schemaCookie, r) ← readBE 4 r
  let (schemaFormat, r) ← readBE 4 r
  let (cacheSize, r) ← readBE 4 r
  let (largestRoot, r) ← readBE 4 r
  let (textEncoding, r) ← readBE 4 r
  let (userVersion, r) ← readBE 4 r
  let (incrementalVacuum, r) ← readBE 4 r
  let (applicationId, r) ← readBE 4 r
  let (z, r) ← take? 20 r
  guard (z = List.replicate 20 0)
  let (versionValidFor, r) ← readBE 4 r
  let (sqliteVersion, _) ← readBE 4 r
  guard (pageSizeOk pageSize && (rv == 1 || rv == 2) && 480 ≤ pageSize - res &&
    schemaFormat ≤ 4 && (textEncoding == 1 || textEncoding == 2 || textEncoding == 3 ||
      textEncoding == 0 && schemaFormat == 0))
  pure { pageSize, writeVersion := wv, readVersion := rv, reserved := res, changeCounter,
         databaseSize, freelistTrunk, freelistCount, schemaCookie, schemaFormat, cacheSize,
         largestRoot, textEncoding, userVersion, incrementalVacuum, applicationId,
         versionValidFor, sqliteVersion }

/-! ## B-tree pages -/

/-- The page type of a flag byte (1.6). -/
def pageType? : Nat → Option PageType
  | 2 => some .indexInterior
  | 5 => some .tableInterior
  | 10 => some .indexLeaf
  | 13 => some .tableLeaf
  | _ => none

/-- The b-tree page header at the start of the input, and the rest. -/
def readPageHeader (b : List UInt8) : Option (PageHeader × List UInt8) := do
  let (flag, r) ← readBE 1 b
  let type ← pageType? flag
  let (firstFreeblock, r) ← readBE 2 r
  let (cellCount, r) ← readBE 2 r
  let (cs, r) ← readBE 2 r
  let (fragmented, r) ← readBE 1 r
  if type.interior then
    let (p, r) ← readBE 4 r
    pure ({ type, firstFreeblock, cellCount, contentStart := if cs = 0 then 65536 else cs,
            fragmented, rightmost := some p }, r)
  else
    pure ({ type, firstFreeblock, cellCount, contentStart := if cs = 0 then 65536 else cs,
            fragmented, rightmost := none }, r)

/-- The `k` two-byte cell pointers at the start of the input. -/
def readPointers : Nat → List UInt8 → Option (List Nat)
  | 0, _ => some []
  | k + 1, b => do
    let (p, r) ← readBE 2 b
    let ps ← readPointers k r
    pure (p :: ps)

/-- How many bytes of a payload of `P` bytes stay on a page of type `t`
    and usable size `U` (1.6). -/
def localOf (t : PageType) (U P : Nat) : Nat :=
  let x := match t with
    | .tableLeaf => U - 35
    | _ => (U - 12) * 64 / 255 - 23
  let m := (U - 12) * 32 / 255 - 23
  if P ≤ x then P
  else
    let k := m + (P - m) % (U - 4)
    if k ≤ x then k else m

/-- A payload of `P` bytes at the start of the input: the bytes on the
    page, the first overflow page if the payload spills, and how many
    bytes that takes. -/
def readPayload (t : PageType) (U P : Nat) (b : List UInt8) :
    Option (List UInt8 × Option Nat × Nat) := do
  let L := localOf t U P
  let (loc, r) ← take? L b
  if L < P then
    let (o, _) ← readBE 4 r
    pure (loc, some o, L + 4)
  else pure (loc, none, L)

/-- A 64-bit two's complement integer from its bits. -/
def int64 (n : Nat) : Int :=
  if n < 9223372036854775808 then n else (n : Int) - 18446744073709551616

/-- The cell at the start of the input, on a page of type `t` and
    usable size `U` (1.6), and how many bytes it takes. -/
def readCell (t : PageType) (U : Nat) (b : List UInt8) : Option (Cell × Nat) :=
  match t with
  | .tableLeaf => do
    let (P, n1, r) ← readVarint b
    let (rowid, n2, r) ← readVarint r
    let (loc, ovf, n3) ← readPayload t U P r
    pure ({ leftChild := none, payloadSize := some P, rowid := some (int64 rowid),
            payload := loc, overflow := ovf }, n1 + n2 + n3)
  | .tableInterior => do
    let (k, r) ← readBE 4 b
    let (rowid, n2, _) ← readVarint r
    pure ({ leftChild := some k, payloadSize := none, rowid := some (int64 rowid),
            payload := [], overflow := none }, 4 + n2)
  | .indexLeaf => do
    let (P, n1, r) ← readVarint b
    let (loc, ovf, n3) ← readPayload t U P r
    pure ({ leftChild := none, payloadSize := some P, rowid := none,
            payload := loc, overflow := ovf }, n1 + n3)
  | .indexInterior => do
    let (k, r) ← readBE 4 b
    let (P, n1, r) ← readVarint r
    let (loc, ovf, n3) ← readPayload t U P r
    pure ({ leftChild := some k, payloadSize := some P, rowid := none,
            payload := loc, overflow := ovf }, 4 + n1 + n3)

/-- The cells at the given offsets of a page, each starting no earlier
    than `start` and ending within `U`. -/
def readCells (t : PageType) (U start : Nat) (page : List UInt8) : List Nat → Option (List Cell)
  | [] => some []
  | p :: ps => do
    guard (start ≤ p)
    let (c, size) ← readCell t U (page.drop p)
    guard (p + size ≤ U)
    let cs ← readCells t U start page ps
    pure (c :: cs)

/-- The `n`th page of a file with header `h`, as a b-tree page (1.6),
    or `none` when it is not in the file or is not a b-tree page this
    reader accepts. -/
def readPage (h : Header) (file : List UInt8) (n : Nat) : Option Page := do
  guard (1 ≤ n)
  let page := (file.drop ((n - 1) * h.pageSize)).take h.pageSize
  guard (page.length = h.pageSize)
  let off := if n = 1 then 100 else 0
  let U := h.pageSize - h.reserved
  let (ph, r) ← readPageHeader (page.drop off)
  let ptrs ← readPointers ph.cellCount r
  let hs := if ph.type.interior then 12 else 8
  guard (off + hs + 2 * ph.cellCount ≤ ph.contentStart && ph.contentStart ≤ U)
  let cells ← readCells ph.type U ph.contentStart page ptrs
  pure { header := ph, pointers := ptrs, cells }

/-! ## Records -/

/-- The content size of a serial type (2.1); `none` for 10 and 11. -/
def sizeOf (t : Nat) : Option Nat :=
  if t ≤ 4 then some t
  else if t = 5 then some 6
  else if t = 6 ∨ t = 7 then some 8
  else if t = 8 ∨ t = 9 then some 0
  else if t = 10 ∨ t = 11 then none
  else some ((t - 12) / 2)

/-- A two's complement integer from big-endian bytes. -/
def signed (c : List UInt8) : Int :=
  let n := bigEndian c
  if 2 * n < 256 ^ c.length then n else (n : Int) - 256 ^ c.length

/-- The value of a column of serial type `t` with contents `c`. -/
def columnValue (t : Nat) (c : List UInt8) : Value :=
  if t = 0 then .null
  else if t ≤ 6 then .int (signed c)
  else if t = 7 then .real (bigEndian c)
  else if t = 8 then .int 0
  else if t = 9 then .int 1
  else if t % 2 = 0 then .blob c
  else .text c

/-- The serial types in a record header, each a varint, to the end of
    the header. `fuel` is the header's length. -/
def readTypes : Nat → List UInt8 → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b => do
    let (t, _, r) ← readVarint b
    let ts ← readTypes fuel r
    pure (t :: ts)

/-- The columns of a record body with these serial types; the body must
    end with the last. -/
def readColumns : List Nat → List UInt8 → Option (List Value)
  | [], [] => some []
  | [], _ :: _ => none
  | t :: ts, b => do
    let size ← sizeOf t
    let (c, r) ← take? size b
    let vs ← readColumns ts r
    pure (columnValue t c :: vs)

/-- The record a payload holds (2.1), or `none` when it is not one. -/
def readRecord (p : List UInt8) : Option (List Value) := do
  let (hsize, n, r) ← readVarint p
  guard (n ≤ hsize)
  let (hdr, body) ← take? (hsize - n) r
  let ts ← readTypes hdr.length hdr
  guard (ts ≠ [])
  readColumns ts body

end Sqlite
