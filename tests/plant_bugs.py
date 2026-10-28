#!/usr/bin/env python3
"""Check that the differential tests catch planted bugs.

Each bug is a one-line change to Sqlite/Basic.lean, or to Main.lean
where its description says so. The script copies the project to a
temporary folder, without .lake/build, plants one bug at a time, runs
tests/run_tests.py there with a small count and without the oracle, and
records how many failures the tests report. So every failure counted is
the tool disagreeing with the model of the file format; SQLite only
makes the databases that are read. Every planted bug must give at least
one failure. The unchanged copy must give none. A bug that stops the
executable from building is not a catch: the tests then give up, and
the bug counts as missed. So is any run that gives up (its record shows
`- Failures: 1 (why)`), a run that dies without writing its record, and
one whose exit status does not match the failures it records. The tests
build only the executable (`lake build sqlite`), so a bug that breaks a
proof still runs.

    python3 tests/plant_bugs.py [--count N]

The script writes tests/PLANTED-BUGS.md and exits non-zero if any bug
goes uncaught.
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "tests" / "PLANTED-BUGS.md"
CODE = "Sqlite/Basic.lean"

# (what the bug does, the text as written, the text with the bug[, file])
BUGS = [
    ("the ninth byte of a varint gives only its low seven bits",
     "      if i = 8 then some (acc * 256 + x.toNat, 9, rest)",
     "      if i = 8 then some (acc * 128 + x.toNat % 128, 9, rest)"),
    ("a byte 0x80 ends a varint, as if its continuation bit were clear",
     "      else if x.toNat < 128 then some (acc * 128 + x.toNat, i + 1, rest)",
     "      else if x.toNat ≤ 128 then some (acc * 128 + x.toNat, i + 1, rest)"),
    ("a varint byte that goes on gives its continuation bit too",
     "      else go (acc * 128 + x.toNat % 128) (i + 1) rest",
     "      else go (acc * 128 + x.toNat) (i + 1) rest"),
    ("the page size 1 is not read as 65536",
     "  let pageSize := if ps = 1 then 65536 else ps",
     "  let pageSize := ps"),
    ("a read version of 0 is accepted",
     "  guard (pageSizeOk pageSize && (rv == 1 || rv == 2) && 480 ≤ pageSize - res &&",
     "  guard (pageSizeOk pageSize && rv ≤ 2 && 480 ≤ pageSize - res &&"),
    ("a usable size of 479 is accepted",
     "  guard (pageSizeOk pageSize && (rv == 1 || rv == 2) && 480 ≤ pageSize - res &&",
     "  guard (pageSizeOk pageSize && (rv == 1 || rv == 2) && 479 ≤ pageSize - res &&"),
    ("only the maximum embedded payload fraction is checked",
     "  guard (fr = [64, 32, 32])",
     "  guard (fr.head? = some 64)"),
    ("the last of the 20 bytes reserved for expansion is not checked",
     "  guard (z = List.replicate 20 0)",
     "  guard (z.take 19 = List.replicate 19 0)"),
    ("schema format 5 is accepted",
     "    schemaFormat ≤ 4 && (textEncoding == 1 || textEncoding == 2 || textEncoding == 3))",
     "    schemaFormat ≤ 5 && (textEncoding == 1 || textEncoding == 2 || textEncoding == 3))"),
    ("text encoding 0 is accepted",
     "    schemaFormat ≤ 4 && (textEncoding == 1 || textEncoding == 2 || textEncoding == 3))",
     "    schemaFormat ≤ 4 && textEncoding ≤ 3)"),
    ("the index leaf page type is 11, not 10",
     "  | 10 => some .indexLeaf",
     "  | 11 => some .indexLeaf"),
    ("page type 2 is read as a table interior page",
     "  | 2 => some .indexInterior",
     "  | 2 => some .tableInterior"),
    ("the right-most pointer is read as 2 bytes",
     "    let (p, r) ← readBE 4 r",
     "    let (p, r) ← readBE 2 r"),
    ("on a leaf page, a content start of 0 is not read as 65536",
     "  else\n    pure ({ type, firstFreeblock, cellCount, contentStart := if cs = 0 then 65536 else cs,",
     "  else\n    pure ({ type, firstFreeblock, cellCount, contentStart := cs,"),
    ("a cell may start one byte before the cell content area",
     "    guard (start ≤ p)",
     "    guard (start ≤ p + 1)"),
    ("a cell may end one byte past the usable size",
     "    guard (p + size ≤ U)",
     "    guard (p + size ≤ U + 1)"),
    ("the bound on the cell pointer array counts one byte a pointer",
     "  guard (off + hs + 2 * ph.cellCount ≤ ph.contentStart && ph.contentStart ≤ U)",
     "  guard (off + hs + ph.cellCount ≤ ph.contentStart && ph.contentStart ≤ U)"),
    ("the cell content area may start in the reserved region",
     "  guard (off + hs + 2 * ph.cellCount ≤ ph.contentStart && ph.contentStart ≤ U)",
     "  guard (off + hs + 2 * ph.cellCount ≤ ph.contentStart && ph.contentStart ≤ h.pageSize)"),
    ("the page header of an interior page is taken as 8 bytes in the bound on the pointer array",
     "  let hs := if ph.type.interior then 12 else 8",
     "  let hs := 8"),
    ("the page may be one byte short of the page size",
     "  guard (page.length = h.pageSize)",
     "  guard (page.length + 1 ≥ h.pageSize)"),
    ("X is U-35 on index leaf pages, not on table leaf pages",
     "    | .tableLeaf => U - 35",
     "    | .indexLeaf => U - 35"),
    ("X on index pages is one more",
     "    | _ => (U - 12) * 64 / 255 - 23",
     "    | _ => (U - 12) * 64 / 255 - 22"),
    ("M divides by 256, not 255",
     "  let m := (U - 12) * 32 / 255 - 23",
     "  let m := (U - 12) * 32 / 256 - 23"),
    ("K takes the remainder by U-5, not U-4",
     "    let k := m + (P - m) % (U - 4)",
     "    let k := m + (P - m) % (U - 5)"),
    ("a K equal to X is not kept on the page",
     "    if k ≤ x then k else m",
     "    if k < x then k else m"),
    ("the overflow page number is read as 3 bytes",
     "    let (o, _) ← readBE 4 r",
     "    let (o, _) ← readBE 3 r"),
    ("a cell that spills is not counted with its overflow page number",
     "    pure (loc, some o, L + 4)",
     "    pure (loc, some o, L)"),
    ("rowids of 2^63 and more are not read as negative",
     "  if n < 9223372036854775808 then n else (n : Int) - 18446744073709551616",
     "  if n < 18446744073709551616 then n else (n : Int) - 18446744073709551616"),
    ("the rowid of a table interior cell is not read as a 64-bit two's complement integer",
     "    pure ({ leftChild := some k, payloadSize := none, rowid := some (int64 rowid),",
     "    pure ({ leftChild := some k, payloadSize := none, rowid := some (rowid : Int),"),
    ("serial type 5 takes 5 bytes, not 6",
     "  else if t = 5 then some 6",
     "  else if t = 5 then some 5"),
    ("serial type 7 is not 8 bytes",
     "  else if t = 6 ∨ t = 7 then some 8",
     "  else if t = 6 then some 8"),
    ("serial type 11 is read",
     "  else if t = 10 ∨ t = 11 then none",
     "  else if t = 10 then none"),
    ("an integer whose top bit is set and the rest clear is read as positive",
     "  if 2 * n < 256 ^ c.length then n else (n : Int) - 256 ^ c.length",
     "  if 2 * n ≤ 256 ^ c.length then n else (n : Int) - 256 ^ c.length"),
    ("serial type 7 is read as an integer",
     "  else if t = 7 then .real (bigEndian c)",
     "  else if t = 7 then .int (signed c)"),
    ("serial type 9 is read as 0",
     "  else if t = 9 then .int 1",
     "  else if t = 9 then .int 0"),
    ("odd serial types are blobs and even ones text",
     "  else if t % 2 = 0 then .blob c",
     "  else if t % 2 = 1 then .blob c"),
    ("the header size is counted after a size varint of one byte, whatever its length",
     "  let (hdr, body) ← take? (hsize - n) r",
     "  let (hdr, body) ← take? (hsize - 1) r"),
    ("bytes after the last column are allowed",
     "  | [], _ :: _ => none",
     "  | [], _ :: _ => some []"),
    ("a record with no column is read",
     "  guard (ts ≠ [])",
     "  guard (ts.length ≥ 0)"),
    ("Main.lean: the CR of a CR LF line ending is kept",
     "    String.ofList (if cs.getLast? = some '\\r' then cs.dropLast else cs)",
     "    String.ofList cs",
     "Main.lean"),
    ("Main.lean: upper-case hex digits are read",
     "  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)",
     "  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)",
     "Main.lean"),
    ("Main.lean: a cell is printed with its rowid before its payload size",
     '  s!"{p}/{opt c.leftChild}/{opt c.payloadSize}/{opt c.rowid}/{toHex c.payload}/{opt c.overflow}"',
     '  s!"{p}/{opt c.leftChild}/{opt c.rowid}/{opt c.payloadSize}/{toHex c.payload}/{opt c.overflow}"',
     "Main.lean"),
    ("Main.lean: the content start 65536 is printed as 0",
     '  s!"{ph.type.code} {ph.firstFreeblock} {ph.cellCount} {ph.contentStart} {ph.fragmented} " ++',
     '  s!"{ph.type.code} {ph.firstFreeblock} {ph.cellCount} {ph.contentStart % 65536} {ph.fragmented} " ++',
     "Main.lean"),
    ("Main.lean: `sqlite dump` exits with 0 when the header is refused",
     '  | none => IO.eprintln "not a database header this reader accepts"; return 1',
     '  | none => IO.eprintln "not a database header this reader accepts"; return 0',
     "Main.lean"),
    ("Main.lean: `sqlite dump` leaves out the last page",
     "    for i in [0:file.length / h.pageSize] do",
     "    for i in [0:file.length / h.pageSize - 1] do",
     "Main.lean"),
    ("Main.lean: `sqlite dump` prints the record of a cell that spills, from the part on the page",
     "          if c.overflow.isNone && !c.payload.isEmpty then",
     "          if !c.payload.isEmpty then",
     "Main.lean"),
]


def failures(copy, count):
    """The failures a run of the tests reports, or None, with the run's
    output, when it reports none: the code did not build, or the run did
    not finish. A run that dies writes no record, so the old one is
    removed first rather than read again."""
    record = copy / "tests" / "TEST-RESULTS.md"
    record.unlink(missing_ok=True)
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count),
                          "--no-oracles"],
                         cwd=copy, capture_output=True, text=True)
    out = run.stdout + run.stderr
    if not record.exists():
        return None, f"no record written, exit status {run.returncode}\n{out}"
    m = re.search(r"^- Failures: (\d+)(.*)$", record.read_text(encoding="utf-8"), re.M)
    if m is None or m.group(2).strip():
        return None, out  # the run gave up, for example the bug did not build: not a catch
    n = int(m.group(1))
    if run.returncode != (1 if n else 0):
        return None, f"{n} failures but exit status {run.returncode}\n{out}"
    return n, None


def ignore(folder, names):
    """Leave out the build, the git folder and old records: the copy
    builds its own executable."""
    leave = {"PLANTED-BUGS.md", "__pycache__", ".git"}
    if Path(folder).resolve() == (ROOT / ".lake").resolve():
        leave.add("build")
    return [n for n in names if n in leave]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=3000)
    args = ap.parse_args()
    rows, missed = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        copy = Path(tmp) / "sqlite"
        shutil.copytree(ROOT, copy, symlinks=True, ignore=ignore)
        n, err = failures(copy, args.count)
        rows.append(("none", n))
        if n != 0:
            missed += 1
        print(f"none: {n} failures" + (" (did not build or did not finish)" if err else ""),
              flush=True)
        if err:
            print(err[-2000:], flush=True)
        for what, line, bug, *where in BUGS:
            name = where[0] if where else CODE
            code = copy / name
            original = code.read_text(encoding="utf-8")
            if original.count(line) != 1:
                sys.exit(f"{name} no longer holds, once, the line for {what!r}: {line}")
            code.write_text(original.replace(line, bug), encoding="utf-8")
            n, err = failures(copy, args.count)
            code.write_text(original, encoding="utf-8")
            rows.append((what, n))
            if not n:
                missed += 1
            print(f"{what}: {n} failures" + (" (did not build or did not finish)" if err else ""),
                  flush=True)
            if err:
                print(err[-2000:], flush=True)
    n_main = sum(1 for b in BUGS if b[3:] == ("Main.lean",))
    lines = ["# Planted bugs", "",
             f"Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `{CODE}` "
             f"({len(BUGS) - n_main} bugs) or to `Main.lean` ({n_main}), tested with "
             f"`tests/run_tests.py --count {args.count} --no-oracles`, which builds only the "
             "executable and compares it with the model alone. Every bug must give failures, and "
             "the unchanged code none. A bug that does not build, or a run that gives up or "
             "dies, counts as missed.", "",
             "| Planted bug | Failures |", "|---|---|"]
    lines += [f"| {what} | {'did not build or did not finish' if n is None else n} |"
              for what, n in rows]
    lines += ["", f"Bugs caught: {sum(1 for what, n in rows[1:] if n)} of {len(BUGS)}", ""]
    RECORD.write_text("\n".join(lines), encoding="utf-8")
    return 1 if missed else 0


if __name__ == "__main__":
    sys.exit(main())
