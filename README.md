# sqlite: reading the SQLite file format, proved

SQLite databases are everywhere: in phones, browsers, operating systems and most desktop programs. A database file is often a file someone else wrote, sent as an attachment, synced from another machine, or recovered from a damaged disk, and programs other than SQLite read it: forensic tools, backup tools, viewers, and readers written in other languages. Each of these takes offsets, sizes and lengths from the file and follows them. A reader that trusts one of them reads past the end of a page or of the file.

This library reads three parts of the format, in Lean:

- the 100-byte database header (1.3 of "Database File Format", https://www.sqlite.org/fileformat2.html);
- one b-tree page: its page header, its cell pointer array, and its cells, with the part of each payload kept on the page by the rule of 1.6;
- records, the format of every row and index entry (2.1), and varints (1.6).

Machine-checked proofs show:

- **The readers accept exactly what the format says, and give back what it holds.** The varint, header, page and record readers each accept an input exactly when it is what `Spec/Defs.lean` writes down from the document, and give the values it holds. The header reader refuses every header that breaks a "must" of 1.3.
- **Nothing the page reader gives lies outside the file or its page.** It refuses page 0 and a page past the end of the file. On a page it gives, the usable part of the page is in the file, the cell pointer array ends before the cell content area starts, and every cell starts in that area and ends within the usable size.
- **The local part of a payload is what the rule of 1.6 gives.** A cell keeps on its page the number of payload bytes the X, M and K rule fixes, and the 4-byte page number of the first overflow page follows exactly when the payload spills.

It is tested against SQLite itself and a model of the document; `tests/TEST-RESULTS.md` holds the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

This reads SQLite files. It is not SQLite, and it is not a database engine.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean, on `List UInt8`, with the structures of `Spec/Defs.lean`:

- `Sqlite.readVarint : List UInt8 → Option (Nat × Nat × List UInt8)`: the varint at the start of the input, its length, and the rest.
- `Sqlite.readHeader : List UInt8 → Option Header`: the database header at the start of a file.
- `Sqlite.readPage : Header → List UInt8 → Nat → Option Page`: page `n` of a file, as a b-tree page.
- `Sqlite.readRecord : List UInt8 → Option (List Value)`: the values of a record.
- `Sqlite.localOf : PageType → Nat → Nat → Nat`: how many bytes of a payload stay on a page.

`SPEC.md` says what each function does.

## What is proved

The statements are in `Spec.lean`. The definitions they use are in `Spec/Defs.lean`, written from sections 1.2, 1.3, 1.6 and 2.1 of the document, and the proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The varint reader accepts exactly an input that starts with a varint of one to nine bytes, and gives its value, its length and what follows. | `Spec.readVarint_iff` |
| The header reader accepts exactly a file that starts with the 100 bytes of a header this reader accepts, and gives that header. | `Spec.readHeader_iff` |
| The page reader gives a page exactly when page `n` is in the file and holds it: the page header, then one cell pointer per cell, then each cell's bytes where its pointer says, within the usable size. | `Spec.readPage_iff` |
| The usable part of every page the reader gives is in the file, and every cell pointer lies after the cell pointer array and before the end of the usable size. | `Spec.readPage_inside` |
| The record reader accepts exactly a record of 2.1 and gives its values. | `Spec.readRecord_iff` |
| Examples worked by hand, and the header SQLite 3.45.1 wrote for a real database, read field by field. Thirteen inputs that each break a rule are refused. | `Spec.examples`, `Spec.rejects` |

The headers this reader accepts are those whose page size is a power of two from 512 to 65536, whose read version is 1 or 2, whose usable size is at least 480, whose payload fractions are 64, 32 and 32, whose schema format is 0 to 4, whose text encoding is 1, 2 or 3 (or 0 in a database with no schema yet, as SQLite writes it), and whose 20 reserved bytes are zero.

## What is not proved

- **Overflow pages.** A payload that spills is given as its local part and the number of its first overflow page. The chain is not followed, so a record that spills is not read; the tests follow it themselves.
- **The b-tree.** Each page is read alone. Nothing checks that child pointers name pages in the file, that keys are in order, or that each page is reached once.
- **Free space.** The freeblock list and the count of fragmented bytes are read but not followed or checked, and nothing checks that cells do not overlap each other or the freeblocks.
- **Other pages.** The freelist, pointer-map pages, the lock-byte page, the WAL and the rollback journal. A page of another kind is refused when it does not read as a b-tree page, but one may happen to read as one.
- **Header fields that need the rest of the file.** The in-header database size, the freelist fields, the schema cookie and the largest root page are read but not checked against the file.
- **Values.** Strings are given as bytes, not checked as UTF-8 or UTF-16; floats are given as their 64 bits.
- **The schema**, and writing a database.
- **Time and memory.** No proof bounds them. The reader works on a list of bytes, so reading page `n` walks the file up to that page.
- **Reading files, requests and printing answers in `Main.lean`.** The differential tests cover them.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number and integer arithmetic, `UInt8`, and lists.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and SQLite, which the record names.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`) and Python 3 with its `sqlite3` module.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

## Layout

- `Sqlite/Basic.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the document.
- `Spec/Examples.lean`: the inputs of the examples: a header SQLite wrote, and a one-page file.
- `Proofs.lean` and `Proofs/`: the proofs.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests and the planted bugs.
