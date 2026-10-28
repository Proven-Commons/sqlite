/-
  The SQLite database file format, written from "Database File Format"
  (https://www.sqlite.org/fileformat2.html): the database header (1.3),
  b-tree pages and their cells (1.6), and the record format (2.1).

  Bytes are `List UInt8`. Multibyte integers in the header, the page
  header, cell pointers and child pointers are big-endian (1.3, 1.6).
  This file uses nothing from the code.
-/

namespace Spec

/-! ## Integers -/

/-- `n` as `w` bytes, most significant first. -/
def beBytes (w n : Nat) : List UInt8 :=
  (List.range w).reverse.map fun i => (n / 256 ^ i % 256).toUInt8

/-- The bytes as an unsigned integer, most significant first. -/
def beNat (bs : List UInt8) : Nat :=
  bs.foldl (fun n b => n * 256 + b.toNat) 0

/-- A varint (1.6): "either zero or more bytes which have the high-order
    bit set followed by a single byte with the high-order bit clear, or
    nine bytes, whichever is shorter". So one to nine bytes; a ninth byte
    may have its high bit set. -/
def Varint (bs : List UInt8) : Prop :=
  1 ≤ bs.length ∧ bs.length ≤ 9 ∧ (∀ b ∈ bs.dropLast, 128 ≤ b.toNat) ∧
    (bs.length < 9 → ∀ b ∈ bs.getLast?, b.toNat < 128)

/-- A varint's value: "The lower seven bits of each of the first eight
    bytes and all 8 bits of the ninth byte are used to reconstruct the
    64-bit twos-complement integer. Varints are big-endian." -/
def varintValue (bs : List UInt8) : Nat :=
  if bs.length = 9 then
    (bs.take 8).foldl (fun n b => n * 128 + b.toNat % 128) 0 * 256 + (bs.getD 8 0).toNat
  else bs.foldl (fun n b => n * 128 + b.toNat % 128) 0

/-- A 64-bit two's complement integer, from its 64 bits as a number. -/
def toInt64 (n : Nat) : Int :=
  if n < 2 ^ 63 then n else (n : Int) - 2 ^ 64

/-! ## The database header (1.3) -/

/-- The header string: "SQLite format 3" and a NUL (1.3.1). -/
def magic : List UInt8 :=
  [0x53, 0x51, 0x4c, 0x69, 0x74, 0x65, 0x20, 0x66, 0x6f, 0x72, 0x6d, 0x61, 0x74, 0x20, 0x33, 0x00]

/-- The fields of the database header, in the order of the table in
    1.3. The page size is the size in bytes. -/
structure Header where
  pageSize : Nat
  writeVersion : Nat
  readVersion : Nat
  reserved : Nat
  changeCounter : Nat
  databaseSize : Nat
  freelistTrunk : Nat
  freelistCount : Nat
  schemaCookie : Nat
  schemaFormat : Nat
  cacheSize : Nat
  largestRoot : Nat
  textEncoding : Nat
  userVersion : Nat
  incrementalVacuum : Nat
  applicationId : Nat
  versionValidFor : Nat
  sqliteVersion : Nat
  deriving DecidableEq, Repr

/-- The usable size of a page: the page size less the reserved space
    (1.3.4). -/
def Header.usable (h : Header) : Nat := h.pageSize - h.reserved

/-- The header as its 100 bytes (1.3). The page size 65536 is written
    as 1 (1.3.2); the payload fractions are 64, 32 and 32 (1.3.5); the
    20 bytes at offset 72 are zero (1.3.17). -/
def headerBytes (h : Header) : List UInt8 :=
  magic ++ beBytes 2 (if h.pageSize = 65536 then 1 else h.pageSize) ++
  [h.writeVersion.toUInt8, h.readVersion.toUInt8, h.reserved.toUInt8, 64, 32, 32] ++
  beBytes 4 h.changeCounter ++ beBytes 4 h.databaseSize ++ beBytes 4 h.freelistTrunk ++
  beBytes 4 h.freelistCount ++ beBytes 4 h.schemaCookie ++ beBytes 4 h.schemaFormat ++
  beBytes 4 h.cacheSize ++ beBytes 4 h.largestRoot ++ beBytes 4 h.textEncoding ++
  beBytes 4 h.userVersion ++ beBytes 4 h.incrementalVacuum ++ beBytes 4 h.applicationId ++
  List.replicate 20 0 ++ beBytes 4 h.versionValidFor ++ beBytes 4 h.sqliteVersion

/-- The headers this reader accepts:
    - a page size that is a power of two from 512 to 65536 (1.2, 1.3.2);
    - a read version of 1 or 2: "If a database file with a read version
      greater than 2 is encountered, then that database cannot be read"
      (1.3.3); any write version, which only makes the file read-only;
    - a usable size of at least 480 (1.3.4);
    - schema format 0 to 4 (1.3.10: formats 1 to 4, and 0 for a database
      with no schema);
    - text encoding 1, 2 or 3 (1.3.13);
    - every field small enough for its bytes. -/
def HeaderValid (h : Header) : Prop :=
  (∃ k, 9 ≤ k ∧ k ≤ 16 ∧ h.pageSize = 2 ^ k) ∧
  h.writeVersion < 256 ∧ (h.readVersion = 1 ∨ h.readVersion = 2) ∧
  h.reserved < 256 ∧ 480 ≤ h.pageSize - h.reserved ∧
  h.changeCounter < 2 ^ 32 ∧ h.databaseSize < 2 ^ 32 ∧ h.freelistTrunk < 2 ^ 32 ∧
  h.freelistCount < 2 ^ 32 ∧ h.schemaCookie < 2 ^ 32 ∧ h.schemaFormat ≤ 4 ∧
  h.cacheSize < 2 ^ 32 ∧ h.largestRoot < 2 ^ 32 ∧
  (h.textEncoding = 1 ∨ h.textEncoding = 2 ∨ h.textEncoding = 3) ∧
  h.userVersion < 2 ^ 32 ∧ h.incrementalVacuum < 2 ^ 32 ∧ h.applicationId < 2 ^ 32 ∧
  h.versionValidFor < 2 ^ 32 ∧ h.sqliteVersion < 2 ^ 32

/-! ## B-tree pages (1.6) -/

/-- The four kinds of b-tree page, by their flag byte. -/
inductive PageType where
  | indexInterior | tableInterior | indexLeaf | tableLeaf
  deriving DecidableEq, Repr

/-- "A value of 2 (0x02) means the page is an interior index b-tree
    page. A value of 5 (0x05) means the page is an interior table b-tree
    page. A value of 10 (0x0a) means the page is a leaf index b-tree
    page. A value of 13 (0x0d) means the page is a leaf table b-tree
    page." -/
def PageType.code : PageType → Nat
  | .indexInterior => 2
  | .tableInterior => 5
  | .indexLeaf => 10
  | .tableLeaf => 13

def PageType.interior : PageType → Bool
  | .indexInterior | .tableInterior => true
  | .indexLeaf | .tableLeaf => false

/-- The b-tree page header (1.6). The start of the cell content area is
    1 to 65536; "A zero value for this integer is interpreted as 65536".
    The right-most pointer is there for interior pages only. -/
structure PageHeader where
  type : PageType
  firstFreeblock : Nat
  cellCount : Nat
  contentStart : Nat
  fragmented : Nat
  rightmost : Option Nat
  deriving DecidableEq, Repr

/-- The page header as its 8 bytes, or 12 for an interior page. -/
def pageHeaderBytes (ph : PageHeader) : List UInt8 :=
  [ph.type.code.toUInt8] ++ beBytes 2 ph.firstFreeblock ++ beBytes 2 ph.cellCount ++
  beBytes 2 (ph.contentStart % 65536) ++ [ph.fragmented.toUInt8] ++
  match ph.rightmost with
  | some p => beBytes 4 p
  | none => []

/-- Every field small enough for its bytes, and a right-most pointer
    exactly on interior pages. -/
def PageHeaderValid (ph : PageHeader) : Prop :=
  ph.firstFreeblock < 2 ^ 16 ∧ ph.cellCount < 2 ^ 16 ∧
  1 ≤ ph.contentStart ∧ ph.contentStart ≤ 65536 ∧ ph.fragmented < 256 ∧
  (match ph.rightmost with
   | some p => ph.type.interior = true ∧ p < 2 ^ 32
   | none => ph.type.interior = false)

/-- "Let X be U-35" on a table leaf page, "Let X be ((U-12)*64/255)-23"
    on an index page: the most payload a cell keeps on its page. -/
def maxLocal (t : PageType) (U : Nat) : Nat :=
  if t = .tableLeaf then U - 35 else (U - 12) * 64 / 255 - 23

/-- "Let M be ((U-12)*32/255)-23". -/
def minLocal (U : Nat) : Nat := (U - 12) * 32 / 255 - 23

/-- How much of a payload of `P` bytes a cell keeps on its page (1.6):
    "If P<=X then all P bytes of payload are stored directly on the
    btree page without overflow. If P>X and K<=X then the first K bytes
    of P are stored on the btree page and the remaining P-K bytes are
    stored on overflow pages. If P>X and K>X then the first M bytes of P
    are stored on the btree page", where K is M+((P-M)%(U-4)). -/
def localSize (t : PageType) (U P : Nat) : Nat :=
  if P ≤ maxLocal t U then P
  else
    let M := minLocal U
    let K := M + (P - M) % (U - 4)
    if K ≤ maxLocal t U then K else M

/-- A cell, with what it holds on its page. A table leaf cell has a
    payload size, a rowid and the payload; a table interior cell a left
    child and a rowid; an index leaf cell a payload size and the payload;
    an index interior cell a left child, a payload size and the payload.
    `payload` is the part of the payload on the page, and `overflow` the
    first overflow page when the rest spills. -/
structure Cell where
  leftChild : Option Nat
  payloadSize : Option Nat
  rowid : Option Int
  payload : List UInt8
  overflow : Option Nat
  deriving DecidableEq, Repr

/-- The payload part of a cell, after its payload size: the bytes kept
    on the page, then "A 4-byte big-endian integer page number for the
    first page of the overflow page list - omitted if all payload fits on
    the b-tree page". -/
def PayloadEncodes (t : PageType) (U P : Nat) (kept : List UInt8) (overflow : Option Nat)
    (bs : List UInt8) : Prop :=
  kept.length = localSize t U P ∧
  if localSize t U P < P then ∃ o, o < 2 ^ 32 ∧ overflow = some o ∧ bs = kept ++ beBytes 4 o
  else overflow = none ∧ bs = kept

/-- `bs` are the bytes of the cell `c` on a page of type `t` and usable
    size `U` (1.6, "B-tree Cell Format"). -/
def CellEncodes (t : PageType) (U : Nat) (c : Cell) (bs : List UInt8) : Prop :=
  match t with
  | .tableLeaf =>
    ∃ vp vr rest, Varint vp ∧ Varint vr ∧ bs = vp ++ vr ++ rest ∧
      c.leftChild = none ∧ c.payloadSize = some (varintValue vp) ∧
      c.rowid = some (toInt64 (varintValue vr)) ∧
      PayloadEncodes t U (varintValue vp) c.payload c.overflow rest
  | .tableInterior =>
    ∃ k vr, k < 2 ^ 32 ∧ Varint vr ∧ bs = beBytes 4 k ++ vr ∧
      c = { leftChild := some k, payloadSize := none, rowid := some (toInt64 (varintValue vr)),
            payload := [], overflow := none }
  | .indexLeaf =>
    ∃ vp rest, Varint vp ∧ bs = vp ++ rest ∧
      c.leftChild = none ∧ c.payloadSize = some (varintValue vp) ∧ c.rowid = none ∧
      PayloadEncodes t U (varintValue vp) c.payload c.overflow rest
  | .indexInterior =>
    ∃ k vp rest, k < 2 ^ 32 ∧ Varint vp ∧ bs = beBytes 4 k ++ vp ++ rest ∧
      c.leftChild = some k ∧ c.payloadSize = some (varintValue vp) ∧ c.rowid = none ∧
      PayloadEncodes t U (varintValue vp) c.payload c.overflow rest

/-- A b-tree page as this reader gives it: its header, its cell
    pointers, and its cells in the order of the pointers. -/
structure Page where
  header : PageHeader
  pointers : List Nat
  cells : List Cell
  deriving DecidableEq, Repr

/-- The cell pointer array: "K 2-byte integer offsets to the cell
    contents". -/
def pointerBytes (ps : List Nat) : List UInt8 :=
  ps.flatMap (beBytes 2)

/-- Where the page header starts: after the 100-byte database header on
    page 1, at the start of every other page (1.6). -/
def headerOffset (n : Nat) : Nat := if n = 1 then 100 else 0

/-- The size of the page header: "8 bytes in size for leaf pages and 12
    bytes for interior pages". -/
def PageType.headerSize (t : PageType) : Nat := if t.interior then 12 else 8

/-- `bytes`, the `n`th page of a file with header `h`, holds the b-tree
    page `pg` (1.6):
    - the page header at its offset, then the cell pointer array, with
      one pointer per cell;
    - the array ends no later than the cell content area starts, and that
      area starts no later than the end of the usable size, the "reserved
      region" coming after it;
    - each cell starts in the cell content area, its bytes are those of
      the cell, and they end within the usable size. -/
def PageEncodes (h : Header) (n : Nat) (pg : Page) (bytes : List UInt8) : Prop :=
  let ph := pg.header
  let off := headerOffset n
  let U := h.usable
  PageHeaderValid ph ∧ ph.cellCount = pg.pointers.length ∧
  pg.cells.length = pg.pointers.length ∧
  (∀ p ∈ pg.pointers, p < 2 ^ 16) ∧
  (bytes.drop off).take (ph.type.headerSize + 2 * pg.pointers.length) =
    pageHeaderBytes ph ++ pointerBytes pg.pointers ∧
  off + ph.type.headerSize + 2 * pg.pointers.length ≤ ph.contentStart ∧ ph.contentStart ≤ U ∧
  ∀ pc ∈ pg.pointers.zip pg.cells, ∃ bs,
    CellEncodes ph.type U pc.2 bs ∧
    ph.contentStart ≤ pc.1 ∧ pc.1 + bs.length ≤ U ∧
    (bytes.drop pc.1).take bs.length = bs

/-- The `n`th page of a file, numbered from 1 (1.2). -/
def pageOf (h : Header) (file : List UInt8) (n : Nat) : List UInt8 :=
  (file.drop ((n - 1) * h.pageSize)).take h.pageSize

/-! ## The record format (2.1) -/

/-- A value of a record. A float is kept as its 64 bits, a string as its
    bytes in the database's text encoding. -/
inductive Value where
  | null
  | int (z : Int)
  | real (bits : Nat)
  | blob (bs : List UInt8)
  | text (bs : List UInt8)
  deriving DecidableEq, Repr

/-- The content size of each serial type ("Serial Type Codes Of The
    Record Format"). Types 10 and 11 are "Reserved for internal use" and
    "will never appear in a well-formed database file". -/
def contentSize (t : Nat) : Option Nat :=
  match t with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4
  | 5 => some 6 | 6 => some 8 | 7 => some 8 | 8 => some 0 | 9 => some 0
  | 10 | 11 => none
  | n => some (if n % 2 = 0 then (n - 12) / 2 else (n - 13) / 2)

/-- A big-endian two's complement integer of the bytes. -/
def signedOf (bs : List UInt8) : Int :=
  if beNat bs < 2 ^ (8 * bs.length - 1) then beNat bs else (beNat bs : Int) - 2 ^ (8 * bs.length)

/-- The value of a column with serial type `t` and content `c`: NULL;
    integers of 1, 2, 3, 4, 6 and 8 bytes; "a big-endian IEEE 754-2008
    64-bit floating point number"; the integers 0 and 1; a BLOB; a
    string. -/
def valueOf (t : Nat) (c : List UInt8) : Value :=
  match t with
  | 0 => .null
  | 1 | 2 | 3 | 4 | 5 | 6 => .int (signedOf c)
  | 7 => .real (beNat c)
  | 8 => .int 0
  | 9 => .int 1
  | n => if n % 2 = 0 then .blob c else .text c

/-- The serial types `ts` and contents `cs` encode the values `vs`, one
    column each. -/
def ColumnsEncode : List (List UInt8) → List (List UInt8) → List Value → Prop
  | [], [], [] => True
  | t :: ts, c :: cs, v :: vs =>
    Varint t ∧ contentSize (varintValue t) = some c.length ∧ v = valueOf (varintValue t) c ∧
      ColumnsEncode ts cs vs
  | _, _, _ => False

/-- `p` is a record of the values `vs` (2.1): "A record contains a
    header and a body, in that order. The header begins with a single
    varint which determines the total number of bytes in the header. The
    varint value is the size of the header in bytes including the size
    varint itself. Following the size varint are one or more additional
    varints, one per column." The body is the contents of the columns,
    one after another, and nothing else. -/
def RecordEncodes (vs : List Value) (p : List UInt8) : Prop :=
  vs ≠ [] ∧ ∃ hs ts cs, Varint hs ∧ varintValue hs = hs.length + ts.flatten.length ∧
    ColumnsEncode ts cs vs ∧ p = hs ++ ts.flatten ++ cs.flatten

end Spec
