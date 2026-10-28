# Specification: sqlite

The SQLite database file format ("Database File Format", https://www.sqlite.org/fileformat2.html) is how every SQLite database is stored. This library reads three parts of it:

- the 100-byte database header (1.3);
- one b-tree page: its page header, its cell pointer array and its cells, with the part of each payload kept on the page (1.6);
- records, the format of every row and index entry (2.1), and the varints they and the cells are made of (1.6).

It does not follow overflow chains, read the freelist, pointer-map pages or the WAL, or check that the pages form a b-tree. "Not in this slice" below lists what else it leaves out.

A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, `Spec/Examples.lean`, and the other files that `bar.toml` lists.

## Varints

`Spec.Varint` is a varint of 1.6: "either zero or more bytes which have the high-order bit set followed by a single byte with the high-order bit clear, or nine bytes, whichever is shorter". So one to nine bytes, and a ninth byte may have its high bit set. `Spec.varintValue` is its value: "The lower seven bits of each of the first eight bytes and all 8 bits of the ninth byte are used to reconstruct the 64-bit twos-complement integer", most significant first. The value is kept as a number from 0 to 2^64 - 1; `Spec.toInt64` reads it as a signed 64-bit integer where 2.1 and 1.6 ask for one (a rowid).

**`Sqlite.readVarint`** accepts exactly the inputs that start with a varint, and gives its value, its length and the bytes after it.

## The database header

`Spec.Header` has the fields of the table in 1.3, in its order, and `Spec.headerBytes` writes them as their 100 bytes: the header string "SQLite format 3" and a NUL, the page size in two bytes (65536 written as 1), the file format write and read versions, the reserved space, the payload fractions 64, 32 and 32, the 4-byte fields, 20 zero bytes, the version-valid-for number and the SQLite version number. Every multibyte field is big-endian.

`Spec.HeaderValid` says which headers this reader accepts. Each rule is a "must" of 1.3, or a value 1.3 says a reader cannot use:

- the page size is a power of two from 512 to 65536 (1.3.2);
- the read version is 1 or 2: "If a database file with a read version greater than 2 is encountered, then that database cannot be read" (1.3.3); any write version is accepted, since it only makes the file read-only;
- the usable size, the page size less the reserved space, is at least 480 (1.3.4);
- the payload fractions are 64, 32 and 32 (1.3.5);
- the schema format is 0 to 4 (1.3.10: formats 1 to 4, and 0 for a database with no schema);
- the text encoding is 1, 2 or 3, for UTF-8, UTF-16le and UTF-16be (1.3.13);
- the 20 bytes "reserved for expansion" are zero (1.3.17);
- every field is small enough for its bytes.

**`Sqlite.readHeader`** accepts exactly the inputs that start with `Spec.headerBytes` of a header in `Spec.HeaderValid`, and gives that header. Since `Spec.headerBytes` is a function of the header, each accepted header comes from exactly one string of 100 bytes.

## B-tree pages

A file is a list of pages of the page size, numbered from 1 (1.2); `Spec.pageOf` is page `n`. Page 1 starts with the database header, so its b-tree page header starts at offset 100; on every other page it starts at 0 (1.6).

**The page header.** `Spec.PageHeader` is the b-tree page header of 1.6: the page type (2, 5, 10 or 13: interior index, interior table, leaf index, leaf table), the first freeblock, the number of cells, the start of the cell content area ("A zero value for this integer is interpreted as 65536"), the number of fragmented free bytes, and the right-most pointer, which interior pages have and leaf pages do not. `Spec.pageHeaderBytes` writes it as its 8 bytes, or 12 on an interior page.

**The cell pointer array.** One 2-byte offset per cell, from the start of the page, after the page header.

**Cells.** `Spec.CellEncodes` writes each kind of cell of "B-tree Cell Format":

- a table leaf cell: the payload size as a varint, the rowid as a varint, the part of the payload kept on the page, and the first overflow page when the payload spills;
- a table interior cell: a 4-byte left child page number and the rowid as a varint;
- an index leaf cell: the payload size, the part kept on the page, and the overflow page;
- an index interior cell: the left child, the payload size, the part kept on the page, and the overflow page.

How much of a payload of `P` bytes stays on the page is `Spec.localSize`, the rule of 1.6 in its own words: with `U` the usable size, `X` is `U-35` on a table leaf page and `((U-12)*64/255)-23` on an index page, `M` is `((U-12)*32/255)-23`, and `K` is `M+((P-M)%(U-4))`. All `P` bytes stay when `P<=X`; else the first `K` when `K<=X`; else the first `M`. When some of the payload spills, a 4-byte page number follows the part on the page.

`Spec.PageEncodes` says that page `n`, with the file's header, holds a page:

- the page header is valid: every field fits its bytes, and the right-most pointer is there exactly on interior pages;
- the page header and then the cell pointer array are at the page header's offset, one pointer per cell;
- the array ends no later than the cell content area starts, and that area starts no later than the end of the usable size;
- each cell starts in the cell content area, its bytes, at the offset its pointer gives, are those of `Spec.CellEncodes`, and they end within the usable size, before the reserved space.

**`Sqlite.readPage`** gives a page exactly when page `n` is in the file and holds it, as `Spec.PageEncodes` says; it refuses page 0 and a page past the end of the file. So nothing it gives lies outside the file or its page: the usable part of the page is in the file, and every cell starts after the cell pointer array and ends within the usable size. A cell's payload is its local part only, with the number of the first overflow page when the payload spills.

## Records

A record (2.1) is a header and a body. The header is a varint giving the size of the header in bytes, the varint itself included, then one varint per column, its serial type. The body is the contents of the columns, one after another. `Spec.contentSize` gives the content size of each serial type, from the table in 2.1, and `Spec.valueOf` the value:

| Serial type | Content size | Value |
|---|---|---|
| 0 | 0 | NULL |
| 1, 2, 3, 4, 5, 6 | 1, 2, 3, 4, 6, 8 | a big-endian two's complement integer |
| 7 | 8 | a 64-bit IEEE 754 float, kept as its 64 bits |
| 8, 9 | 0 | the integers 0 and 1 |
| 10, 11 | | "will never appear in a well-formed database file": refused |
| N ≥ 12, even | (N-12)/2 | a BLOB |
| N ≥ 13, odd | (N-13)/2 | a string, as its bytes in the database's text encoding |

`Spec.RecordEncodes vs p` says that `p` is a record of the values `vs`: at least one column ("one or more additional varints, one per column"), a header size that is the size of the header, and a body that is exactly the contents of the columns.

**`Sqlite.readRecord`** accepts exactly the records and gives their values.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| The varint reader accepts exactly an input that starts with a varint, and gives its value, its length and what follows. | `Spec.readVarint_iff` |
| The header reader accepts exactly a file that starts with the 100 bytes of a header in `Spec.HeaderValid`, and gives that header. | `Spec.readHeader_iff` |
| The page reader gives a page exactly when page `n` is in the file and holds it, as `Spec.PageEncodes` says. | `Spec.readPage_iff` |
| The usable part of every page the reader gives is in the file, and every cell pointer lies after the cell pointer array and before the end of the usable size. | `Spec.readPage_inside` |
| The record reader accepts exactly a record and gives its values. | `Spec.readRecord_iff` |
| Examples worked by hand: varints of one, two and nine bytes; the local size of a payload of 10000 bytes on a table leaf page of usable size 4096; a record of an integer and a string; the header SQLite 3.45.1 wrote for a database, field by field; and a one-page file with one row. | `Spec.examples` |
| Inputs that each break a rule: a varint cut short; a header without its header string, with a page size of 768, a read version of 3, a usable size of 479, a text encoding of 0, or a payload fraction of 63; page 2 of a one-page file, and page 0; serial type 10, a body longer than its columns, a header size larger than the record, and a record with no column. | `Spec.rejects` |

## Not in this slice

- **Overflow pages.** A payload that spills is given as its local part and the number of its first overflow page; the chain is not followed, so a record that spills is not read.
- **The b-tree.** Each page is read alone. Nothing checks that child pointers name pages in the file, that keys are in order, or that each page is reached once.
- **Free space.** The freeblock list and the count of fragmented bytes are read but not followed or checked, and nothing checks that cells do not overlap each other or the freeblocks.
- **Other pages.** The freelist, pointer-map pages, the lock-byte page, and the WAL and rollback journal. A page of another kind is refused when it does not read as a b-tree page, but one may happen to read as one.
- **Header fields that need the rest of the file.** The in-header database size, the freelist fields, the schema cookie and the largest root page are read but not checked against the file.
- **Values.** Strings are given as bytes and not checked as UTF-8 or UTF-16; floats are given as their 64 bits.
- **The schema.** Which b-tree belongs to which table, and the SQL in `sqlite_schema`.
- **Writing a database.**

## The command-line tool

`Main.lean` has two modes:

- `sqlite dump FILE` prints the header of a database file, then each page as a b-tree page (or `page N FAIL`), and the record of each cell whose payload is all on its page. It exits with 1 when the file does not start with a header this reader accepts, and with 2 on wrong arguments or a file it cannot read.
- `sqlite serve` answers requests from the differential tests, one per line. The header comment of `Main.lean` gives the protocol.

Every answer comes from the functions above.
