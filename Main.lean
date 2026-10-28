/-
  Command line front end.

    sqlite dump FILE

  reads a database file and prints its header, then each page in turn:
  the page as a b-tree page, or `page N FAIL` when it is not one this
  reader accepts, and, for each cell whose payload is all on its page,
  the record it holds. It exits with 1 when the file does not start
  with a header this reader accepts, and with 2 on wrong arguments or a
  file it cannot read.

    sqlite serve

  answers requests on standard input, one per line, for the
  differential tests. Bytes are hex digits, two per byte, and an empty
  field is written `-`. Numbers are decimal.

    varint HEX       prints  OK, the value, the length and the hex of the
                             rest, or FAIL                  (readVarint)
    header HEX       prints  OK and the 18 fields, or FAIL  (readHeader)
    page N HEX       prints  OK and page N of the file HEX, read with the
                             file's own header, or FAIL     (readPage)
    record HEX       prints  OK and the values, or FAIL     (readRecord)
    local T U P      prints  OK and how many bytes of a payload of P
                             bytes stay on a page of type T (2, 5, 10
                             or 13) and usable size U       (localOf)

  A page is written as its type, first freeblock, cell count, content
  start, fragmented bytes and right-most pointer (`-` on a leaf page),
  then `|`, then its cells, separated by spaces. A cell is written as
  its pointer, left child, payload size, rowid, payload hex and
  overflow page, separated by `/`, with `-` for a field the cell does
  not have. A value is written `null`, `int:Z`, `real:BITS` (the 64
  bits as a decimal number), `blob:HEX` or `text:HEX`.

  A malformed request prints `error`: an unknown operation, the wrong
  number of fields, hex digits that are not in pairs or not lower case,
  or a number that is not decimal. A request line may end in LF or
  CR LF.

  Every answer comes from the proved functions in `Sqlite/`. The hex
  coding, the output and the request handling here are covered by the
  tests, not by a proof.
-/

import Sqlite

open Sqlite Spec

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- Bytes from hex digits in pairs. Tail recursive, so that long inputs
    do not use the stack. -/
def hexBytes (cs : List Char) (acc : Array UInt8) : Option (Array UInt8) :=
  match cs with
  | [] => some acc
  | a :: b :: rest =>
    match hexValue a, hexValue b with
    | some hi, some lo => hexBytes rest (acc.push (hi * 16 + lo).toUInt8)
    | _, _ => none
  | [_] => none

/-- The bytes a field gives: `-` for none, else hex digits in pairs. -/
def fromHex (f : String) : Option (List UInt8) :=
  if f = "-" then some [] else if f.isEmpty then none else (hexBytes f.toList #[]).map (·.toList)

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- A field for a list of bytes: `-` when it is empty. -/
def toHex (bs : List UInt8) : String :=
  if bs.isEmpty then "-"
  else String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- A decimal number, without sign or leading `+`. -/
def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

def opt {α} [ToString α] : Option α → String
  | some a => toString a
  | none => "-"

def showHeader (h : Header) : String :=
  " ".intercalate (List.map toString [h.pageSize, h.writeVersion, h.readVersion, h.reserved,
    h.changeCounter, h.databaseSize, h.freelistTrunk, h.freelistCount, h.schemaCookie,
    h.schemaFormat, h.cacheSize, h.largestRoot, h.textEncoding, h.userVersion,
    h.incrementalVacuum, h.applicationId, h.versionValidFor, h.sqliteVersion])

def showCell (p : Nat) (c : Cell) : String :=
  s!"{p}/{opt c.leftChild}/{opt c.payloadSize}/{opt c.rowid}/{toHex c.payload}/{opt c.overflow}"

def showPage (pg : Page) : String :=
  let ph := pg.header
  let cells := (pg.pointers.zip pg.cells).map fun (p, c) => showCell p c
  s!"{ph.type.code} {ph.firstFreeblock} {ph.cellCount} {ph.contentStart} {ph.fragmented} " ++
    s!"{opt ph.rightmost} |" ++ String.join (cells.map (" " ++ ·))

def showValue : Value → String
  | .null => "null"
  | .int z => s!"int:{z}"
  | .real b => s!"real:{b}"
  | .blob bs => s!"blob:{toHex bs}"
  | .text bs => s!"text:{toHex bs}"

def showValues (vs : List Value) : String := " ".intercalate (vs.map showValue)

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["varint", h] => do
    let b ← fromHex h
    pure (match readVarint b with
      | some (v, k, rest) => s!"OK {v} {k} {toHex rest}"
      | none => "FAIL")
  | ["header", h] => do
    let b ← fromHex h
    pure (match readHeader b with
      | some hd => s!"OK {showHeader hd}"
      | none => "FAIL")
  | ["page", n, h] => do
    let n ← decimal n
    let b ← fromHex h
    pure (match readHeader b >>= fun hd => readPage hd b n with
      | some pg => s!"OK {showPage pg}"
      | none => "FAIL")
  | ["record", h] => do
    let b ← fromHex h
    pure (match readRecord b with
      | some vs => s!"OK {showValues vs}"
      | none => "FAIL")
  | ["local", t, u, p] => do
    let t ← (decimal t).bind pageType?
    let u ← decimal u
    let p ← decimal p
    pure s!"OK {localOf t u p}"
  | _ => none

/-- A request line without its line ending, LF or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")
    stdout.flush

/-- The header, then each page and the records of its cells. -/
def dump (file : List UInt8) : IO UInt32 := do
  match readHeader file with
  | none => IO.eprintln "not a database header this reader accepts"; return 1
  | some h =>
    IO.println s!"header {showHeader h}"
    for i in [0:file.length / h.pageSize] do
      let n := i + 1
      match readPage h file n with
      | none => IO.println s!"page {n} FAIL"
      | some pg =>
        IO.println s!"page {n} {showPage pg}"
        for (p, c) in pg.pointers.zip pg.cells do
          if c.overflow.isNone && !c.payload.isEmpty then
            match readRecord c.payload with
            | some vs => IO.println s!"record {n} {p} {opt c.rowid} {showValues vs}"
            | none => IO.println s!"record {n} {p} {opt c.rowid} FAIL"
    return 0

def usage : String := "usage: sqlite dump FILE\n       sqlite serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", path] =>
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .error e => IO.eprintln s!"cannot read {path}: {e}"; return 2
    | .ok bytes => dump bytes.toList
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
