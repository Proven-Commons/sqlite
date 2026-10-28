#!/usr/bin/env python3
"""Differential tests: the Lean reader of the SQLite file format against
a model of the format and against SQLite itself.

The tool answers `varint`, `header`, `page`, `record` and `local`
requests, and prints a whole file with `sqlite dump FILE` (see the
header of Main.lean). Its answers are checked two ways.

1. Against the model, a Python reader written from "Database File
   Format" (https://www.sqlite.org/fileformat2.html), sections 1.3, 1.6
   and 2.1, that shares nothing with the Lean code:
   - varints as 1.6 gives them: one to nine bytes, the first eight
     giving their low seven bits and ending the varint when their high
     bit is clear, a ninth giving all eight;
   - the 100-byte header as the table of 1.3 lays it out, big-endian,
     with the page size 1 read as 65536 (1.3.2);
   - a b-tree page as 1.6 lays it out: the page header after the
     database header on page 1, at the start of every other page; the
     right-most pointer on interior pages only; a content start of 0
     read as 65536; the cell pointer array; and each cell as the cell
     table of 1.6 gives it, with the part of its payload kept on the
     page worked out from X, M and K, and the first overflow page when
     the payload spills;
   - records as 2.1 gives them: the header size, one serial type per
     column, and the body.
   Where 1.3 says a field "must" hold a value, or a page or record could
   be read more loosely than 1.6 and 2.1 say, the model follows the
   choices Spec/Defs.lean writes down for this reader, which are
   stricter than SQLite in places:
   - HeaderValid: the header string; a page size that is a power of two
     from 512 to 65536; a read version of 1 or 2 (any write version); a
     usable size of at least 480; payload fractions of exactly 64, 32
     and 32; the 20 bytes reserved for expansion all zero; a schema
     format from 0 to 4; a text encoding of 1, 2 or 3;
   - PageEncodes: a page type of 2, 5, 10 or 13; the cell pointer array
     ending no later than the cell content area starts, and that area
     starting no later than the usable size; every cell starting no
     earlier than the content area and ending within the usable size;
   - RecordEncodes: serial types 10 and 11 refused; a body of exactly
     the columns, no byte more; at least one column; every serial type
     ending within the header.
   The `local` request is `localSize`, in natural numbers as
   Spec/Defs.lean computes it, so a difference below 0 is 0 and a
   remainder by 0 is the number itself. `dump` is the header, then each
   whole page, read or `FAIL`, and the record of each cell whose
   payload is all on its page, as the header of Main.lean says. The
   model must give the answers Spec.lean states in `examples` and
   `rejects`. Every answer of the tool must equal the model's. The
   record counts, for each kind of request, why the model refuses what
   it refuses.

2. Against SQLite: Python's sqlite3 module, linked to the SQLite library
   SQLITE_PINNED, makes databases of many kinds (see below) and then
   answers questions about them in SQL. The tool reads each file with
   `sqlite dump`, and the harness checks:
   - the header fields against the PRAGMAs page_size, page_count,
     freelist_count, schema_version, user_version, application_id,
     encoding, default_cache_size, journal_mode (versions 1, or 2 for
     WAL), auto_vacuum (the largest root page and the incremental vacuum
     flag), and sqlite_version();
   - every row of the dbstat virtual table: the harness walks each
     b-tree from the root page sqlite_schema gives, by the child
     pointers the tool reads, and follows each overflow chain from the
     first overflow page the tool reads (the next page number is the
     first 4 bytes of each overflow page, 1.7). From that it rebuilds
     what dbstat gives for every page: the b-tree it belongs to, its
     path, whether it is an interior, leaf or overflow page, its cells,
     the payload bytes on it (the sum of the parts the tool keeps on the
     page), its unused bytes, and its largest payload. The types the
     tool reads must be table types in a table b-tree and index types in
     an index or a WITHOUT ROWID table, and each overflow chain must end
     where the payload size says. The key of each table interior cell
     must be no less than the rowids to its left and less than those to
     its right (1.6);
   - that every page is accounted for, once: a page dbstat lists, a
     freelist page reached from the first trunk page the tool reads
     (1.5), or a pointer-map page (1.8); that the pages SQLite does not
     read as b-tree pages are not read as b-tree pages by the tool; and
     that each pointer-map entry gives the parent the tool's reading
     gives;
   - every row of every rowid table, sqlite_schema among them, against
     SELECT rowid, * in rowid order: the rowids the tool reads, and the
     values of the records. A cell whose payload is all on its page is
     read from the dump; for one that spills, the harness joins the part
     on the page and the overflow pages, as many as the payload size
     needs, and asks the tool's `record` request to read the whole
     payload. So the tool's split of the payload must be where SQLite
     put the bytes, or the record does not read back;
   - every entry of every index and WITHOUT ROWID table, against SELECT
     of the columns PRAGMA index_xinfo lists, as multisets.
   Text is compared as bytes in the database's encoding, a float as its
   64 bits, a blob as its bytes.

   A disagreement is allowed only for a named reason that the model
   confirms: the model's reading, with SQLite's own rule, gives SQLite's
   answer. The rules:
   - an INTEGER PRIMARY KEY column is NULL in the record, and SQLite
     gives the rowid for it (2.3);
   - in a column of REAL affinity, a float with no fractional part is
     kept as an integer, and SQLite gives it back as a float (2.3);
   - user_version and application_id read their 4 bytes as a signed
     integer;
   - default_cache_size gives SQLite's built-in default, -2000, for a
     field of 0;
   - dbstat counts the unused bytes of a page from the content start as
     stored, so a 0 counts as 0 and not as 65536 (1.6);
   - SQLite knows overflow, freelist and pointer-map pages by where they
     are linked from, not by their bytes, and some of them hold bytes
     that read as a b-tree page; the model reads them the same way;
   - SQLite writes a text encoding of 0 while a database has no schema,
     and reads it as UTF-8. The model, after Spec/Defs.lean, refuses
     such a header; read with SQLite's rule for that one field, it gives
     the PRAGMAs.
   Any other disagreement is a failure. The record gives each named
   difference with its count and the first case. If the installed
   SQLite is not SQLITE_PINNED or has no dbstat, SQLite is left out as
   an oracle, and the record says so on its `- Oracles left out:` line.

Inputs come from a recorded seed:

- databases made by SQLite: a fixed set (FIXED_DATABASES) and random
  ones, with page sizes from 512 to 65536, reserved bytes at the end of
  each page (set with SQLITE_FILECONTROL_RESERVE_BYTES through ctypes,
  on the library the sqlite3 module uses), UTF-8 and UTF-16 text,
  auto_vacuum and incremental vacuum (pointer-map pages), WAL, the
  legacy file format (schema format 1, set with
  SQLITE_DBCONFIG_LEGACY_FILE_FORMAT), secure_delete off,
  user_version, application_id and default_cache_size; tables with and
  without rowid, STRICT tables, INTEGER PRIMARY KEY, AUTOINCREMENT, a
  table of 70 columns, indexes (UNIQUE, DESC, COLLATE, partial);
  integers of every size and sign around each boundary, 0 and 1,
  floats, NULL, text and blobs from empty to big enough for long
  overflow chains; payload sizes on both sides of each place where the
  part kept on the page changes; rows enough for interior pages;
  explicit negative and huge rowids; deletes and updates that leave
  freeblocks, fragments and free pages; dropped tables, VACUUM,
  ANALYZE, views and triggers. Each is dumped, and so is a copy of some
  of them with bytes changed;
- pages of those databases asked with `page N`: the first pages of
  each, with the file cut after the page, page 0, the last page and the
  one after it; pages moved to page 2 of a two-page file, whole and one
  byte short; and pages
  changed in one way: a bit flipped, a page header byte, the cell count,
  the content start, a cell pointer, a payload size, a rowid, an
  overflow page number, the right-most pointer, the page type, a byte
  of a cell, the freeblock and fragment fields, the reserved byte or
  the page size field of the header, or the file cut short;
- b-tree pages built from their parts, of every type and page size,
  with payload sizes around X, M and K, and with defects: the content
  start before the pointer array ends, past the usable size, 0, or past
  the first cell; a cell pointer before the content area; a cell running
  past the usable size; the cell count one more or one less; and pages
  at the edges of PageEncodes, empty or with one cell, for three page
  sizes with and without reserved bytes, whole and one byte short;
- every value of every byte of two real headers, every value of the
  page size field, every value of the versions, the reserved byte and
  the payload fractions for each page size, headers from random fields,
  a real header cut short;
- every varint of one and two bytes, each length at its bounds, nine
  bytes with every ninth byte, and random bytes;
- random records, with integers stored in their fewest bytes and in
  more, floats, text, blobs, 0 and 1, header varints in more bytes than
  needed; and changed: serial types 10, 11 and huge ones, the body one
  byte longer or shorter, no body, the header size one off, smaller
  than its varint or past the record, a serial type running past the
  header, no column, a bit flipped; and random bytes;
- `local` over a grid of page types, usable sizes (0 to 40, around 480
  and 512, each page size less some reserved bytes, and huge ones) and
  payload sizes around X, M and K, every payload size up to three pages
  for two usable sizes, and random ones;
- the inputs of Spec.lean's `examples` and `rejects`;
- malformed requests, which the tool must answer with `error`, and odd
  but well-formed ones;
- the command line: `sqlite dump` on a database, on a file with no
  header, an empty file, a header alone, a file cut inside its header,
  a file with part of a page at the end, a file that does not exist and
  a folder; `sqlite serve` with nothing to read; and wrong arguments:
  what each run prints on standard output and its exit status.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N] [--no-oracles] [--no-build]

`--count` is the number of random varints and records; a fifth as many
random headers and built pages, a third as many changed pages, half as
many random `local` requests, and `--count` / 1000 random databases
after the fixed ones are made. `--no-oracles` leaves SQLite out as an
oracle and compares the tool with the model alone, as
tests/plant_bugs.py does; the databases are still made, as inputs. The
script builds the executable with `lake build sqlite` first, or, with
`--no-build`, takes the one in .lake/build/bin as it is, for when
another process owns the build; either way it runs a copy, so a build
during the run cannot change it. It writes tests/TEST-RESULTS.md and
exits non-zero if any check fails.
"""

import argparse
import collections
import concurrent.futures
import ctypes
import hashlib
import os
import random
import shutil
import sqlite3
import struct
import subprocess
import sys
import sysconfig
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILT_EXE = ROOT / ".lake" / "build" / "bin" / "sqlite"
TESTS = ROOT / "tests"
RESULTS = TESTS / "TEST-RESULTS.md"
TIMEOUT = 3600
BUILD_TIMEOUT = 3600
SQLITE_PINNED = "3.45.1"
# The requests are split among this many `sqlite serve` processes, and
# this many dumps run at once.
JOBS = max(1, min(4, os.cpu_count() or 1))
# The copy of the executable the run uses (set in main).
EXE = None

# ---------------------------------------------------------------------
# The model: "Database File Format", sections 1.3, 1.6 and 2.1, with the
# choices of Spec/Defs.lean.

MAGIC = b"SQLite format 3\x00"
PAGE_SIZES = (512, 1024, 2048, 4096, 8192, 16384, 32768, 65536)
INDEX_INTERIOR, TABLE_INTERIOR, INDEX_LEAF, TABLE_LEAF = 2, 5, 10, 13
PAGE_TYPES = (INDEX_INTERIOR, TABLE_INTERIOR, INDEX_LEAF, TABLE_LEAF)
INTERIOR = (INDEX_INTERIOR, TABLE_INTERIOR)

# The fields of a header, in the order of the table in 1.3.
H_PAGE_SIZE, H_WRITE, H_READ, H_RESERVED, H_CHANGE, H_SIZE, H_TRUNK, H_FREE, H_COOKIE, \
    H_SCHEMA, H_CACHE, H_LARGEST, H_ENCODING, H_USER, H_INCREMENTAL, H_APPID, H_VALID, \
    H_VERSION = range(18)


def nsub(a, b):
    """a - b in natural numbers, as Spec/Defs.lean computes it."""
    return a - b if a > b else 0


def ndiv(a, b):
    return a // b if b else 0


def nmod(a, b):
    return a % b if b else a


def be(bs):
    """Bytes as a big-endian unsigned integer."""
    return int.from_bytes(bs, "big")


def read_varint(b, pos=0, end=None):
    """The varint at `pos`, reading no byte at or past `end`: its value
    and length, or None when the bytes end first (1.6). "A varint is
    between 1 and 9 bytes in length. The varint consists of either zero
    or more bytes which have the high-order bit set followed by a single
    byte with the high-order bit clear, or nine bytes, whichever is
    shorter. The lower seven bits of each of the first eight bytes and
    all 8 bits of the ninth byte are used to reconstruct the 64-bit
    twos-complement integer. Varints are big-endian." """
    end = len(b) if end is None else end
    v = 0
    for i in range(9):
        if pos + i >= end:
            return None
        x = b[pos + i]
        if i == 8:
            return (v << 8) | x, 9
        v = (v << 7) | (x & 0x7F)
        if x < 0x80:
            return v, i + 1
    raise AssertionError("unreachable")


WHY_H_SHORT = "fewer than 100 bytes (1.3)"
WHY_H_MAGIC = "not the header string (1.3.1)"
WHY_H_PAGE_SIZE = "a page size that is not a power of two from 512 to 65536 (1.3.2)"
WHY_H_READ = "a read version other than 1 and 2 (1.3.3)"
WHY_H_FRACTIONS = "payload fractions other than 64, 32 and 32 (1.3.5)"
WHY_H_USABLE = "a usable size below 480 (1.3.4)"
WHY_H_SCHEMA = "a schema format above 4 (1.3.10)"
WHY_H_ENCODING = "a text encoding other than 1, 2 and 3 (1.3.13)"
WHY_H_EXPANSION = "the 20 bytes reserved for expansion not all zero (1.3.17)"


def read_header(f, encoding_zero=False):
    """The 18 fields of the database header at the start of `f`, in the
    order of the table in 1.3, and None; or None and why it is refused.
    With `encoding_zero`, a text encoding of 0 is read too, as SQLite
    does: it writes 0 there while a database has no schema, and reads
    it as UTF-8."""
    if len(f) < 100:
        return None, WHY_H_SHORT
    if f[:16] != MAGIC:
        return None, WHY_H_MAGIC
    # "Must be a power of two between 512 and 32768 inclusive, or the
    # value 1 representing a page size of 65536."
    stored = be(f[16:18])
    page_size = 65536 if stored == 1 else stored
    if page_size not in PAGE_SIZES:
        return None, WHY_H_PAGE_SIZE
    write_version, read_version, reserved = f[18], f[19], f[20]
    # "If a database file with a read version greater than 2 is
    # encountered, then that database cannot be read or written."
    if read_version not in (1, 2):
        return None, WHY_H_READ
    # "The maximum and minimum embedded payload fractions and the leaf
    # payload fraction values must be 64, 32, and 32."
    if f[21:24] != bytes([64, 32, 32]):
        return None, WHY_H_FRACTIONS
    # "the usable size is not allowed to be less than 480"
    if page_size - reserved < 480:
        return None, WHY_H_USABLE
    words = [be(f[i:i + 4]) for i in range(24, 72, 4)]
    if words[H_SCHEMA - 4] > 4:
        return None, WHY_H_SCHEMA
    if words[H_ENCODING - 4] not in ((0, 1, 2, 3) if encoding_zero else (1, 2, 3)):
        return None, WHY_H_ENCODING
    # "Reserved for expansion. Must be zero."
    if any(f[72:92]):
        return None, WHY_H_EXPANSION
    return (page_size, write_version, read_version, reserved, *words, be(f[92:96]),
            be(f[96:100])), None


def max_local(t, U):
    """X: "U-35" on a table leaf page, "((U-12)*64/255)-23" on the
    others."""
    if t == TABLE_LEAF:
        return nsub(U, 35)
    return nsub(ndiv(nsub(U, 12) * 64, 255), 23)


def min_local(U):
    """M: "((U-12)*32/255)-23"."""
    return nsub(ndiv(nsub(U, 12) * 32, 255), 23)


def local_size(t, U, P):
    """How many bytes of a payload of P bytes stay on a page of type t
    and usable size U (1.6): "If P<=X then all P bytes of payload are
    stored directly on the btree page without overflow. If P>X and K<=X
    then the first K bytes of P are stored on the btree page ... If P>X
    and K>X then the first M bytes of P are stored on the btree page",
    with K = M+((P-M)%(U-4))."""
    X = max_local(t, U)
    if P <= X:
        return P
    M = min_local(U)
    K = M + nmod(nsub(P, M), nsub(U, 4))
    return K if K <= X else M


def int64(n):
    """A 64-bit two's complement integer from its bits."""
    return n - (1 << 64) if n >= 1 << 63 else n


def read_cell(t, U, page, p):
    """The cell at offset p of a page of type t, reading no byte at or
    past the usable size U: (left child, payload size, rowid, the part
    of the payload on the page, first overflow page), and its length;
    or None. The parts, in order (1.6): a table leaf cell has the
    payload size, the rowid, the payload; a table interior cell the left
    child and the rowid; an index leaf cell the payload size and the
    payload; an index interior cell the left child, the payload size and
    the payload; a payload that spills is followed by "A 4-byte
    big-endian integer page number for the first page of the overflow
    page list"."""
    pos = p
    left = size = rowid = overflow = None
    kept = b""
    if t in INTERIOR:
        if pos + 4 > U:
            return None
        left = be(page[pos:pos + 4])
        pos += 4
    if t != TABLE_INTERIOR:
        r = read_varint(page, pos, U)
        if r is None:
            return None
        size, k = r
        pos += k
    if t in (TABLE_LEAF, TABLE_INTERIOR):
        r = read_varint(page, pos, U)
        if r is None:
            return None
        rowid = int64(r[0])
        pos += r[1]
    if t != TABLE_INTERIOR:
        L = local_size(t, U, size)
        if pos + L > U:
            return None
        kept = bytes(page[pos:pos + L])
        pos += L
        if L < size:
            if pos + 4 > U:
                return None
            overflow = be(page[pos:pos + 4])
            pos += 4
    return (left, size, rowid, kept, overflow), pos - p


WHY_P_HEADER = "the file's header is refused"
WHY_P_ZERO = "page 0: pages are numbered from 1 (1.2)"
WHY_P_PAST = "the page is not all in the file (1.2)"
WHY_P_TYPE = "a page type other than 2, 5, 10 and 13 (1.6)"
WHY_P_ARRAY = "the cell pointer array runs past the start of the cell content area (1.6)"
WHY_P_CONTENT = "the cell content area starts past the usable size (1.6)"
WHY_P_CELL_START = "a cell starts before the cell content area (1.6)"
WHY_P_CELL_END = "a cell runs past the usable size (1.6)"


def read_page(h, f, n):
    """Page n of the file f with header h, as a b-tree page: (type, first
    freeblock, cell count, content start, fragmented bytes, right-most
    pointer, cell pointers, cells), and None; or None and why."""
    ps = h[H_PAGE_SIZE]
    if n < 1:
        return None, WHY_P_ZERO
    start = (n - 1) * ps
    if start + ps > len(f):
        return None, WHY_P_PAST
    page = f[start:start + ps]
    # "The 100-byte database file header is found only on page 1"
    off = 100 if n == 1 else 0
    U = ps - h[H_RESERVED]
    t = page[off]
    if t not in PAGE_TYPES:
        return None, WHY_P_TYPE
    hs = 12 if t in INTERIOR else 8
    first_freeblock = be(page[off + 1:off + 3])
    count = be(page[off + 3:off + 5])
    # "A zero value for this integer is interpreted as 65536."
    content = be(page[off + 5:off + 7]) or 65536
    fragmented = page[off + 7]
    right = be(page[off + 8:off + 12]) if t in INTERIOR else None
    if off + hs + 2 * count > content:
        return None, WHY_P_ARRAY
    if content > U:
        return None, WHY_P_CONTENT
    pointers = [be(page[off + hs + 2 * i:off + hs + 2 * i + 2]) for i in range(count)]
    cells = []
    for p in pointers:
        if p < content:
            return None, WHY_P_CELL_START
        c = read_cell(t, U, page, p)
        if c is None:
            return None, WHY_P_CELL_END
        cells.append(c[0])
    return (t, first_freeblock, count, content, fragmented, right, pointers, cells), None


# "Serial Type Codes Of The Record Format": the content size of types 0
# to 9; 10 and 11 are "Reserved for internal use".
FIXED_SIZES = {0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 6, 6: 8, 7: 8, 8: 0, 9: 0}


def content_size(t):
    if t in FIXED_SIZES:
        return FIXED_SIZES[t]
    if t in (10, 11):
        return None
    return (t - 12) // 2 if t % 2 == 0 else (t - 13) // 2


def hx(b):
    """Bytes as `sqlite serve` writes them: hex, or `-` for none."""
    return bytes(b).hex() or "-"


def value_of(t, c):
    """The value of a column of serial type t with content c, written as
    `sqlite serve` writes it."""
    if t == 0:
        return "null"
    if t <= 6:
        return f"int:{int.from_bytes(c, 'big', signed=True)}"
    if t == 7:
        return f"real:{be(c)}"
    if t == 8:
        return "int:0"
    if t == 9:
        return "int:1"
    return ("blob:" if t % 2 == 0 else "text:") + hx(c)


WHY_R_SIZE_ENDS = "the header size varint does not end (2.1)"
WHY_R_SIZE_SMALL = "a header size smaller than its own varint (2.1)"
WHY_R_SIZE_PAST = "a header size past the end of the record (2.1)"
WHY_R_TYPE_PAST = "a serial type runs past the end of the header (2.1)"
WHY_R_NO_COLUMN = "no column (2.1: \"one or more additional varints\")"
WHY_R_RESERVED = "serial type 10 or 11, \"Reserved for internal use\" (2.1)"
WHY_R_SHORT = "the body ends before the last column (2.1)"
WHY_R_LONG = "bytes after the last column (Spec/Defs.lean RecordEncodes)"


def read_record(p):
    """The values of the record p (2.1), and None; or None and why. "The
    header begins with a single varint which determines the total number
    of bytes in the header. The varint value is the size of the header
    in bytes including the size varint itself. Following the size varint
    are one or more additional varints, one per column." The values of
    the columns follow the header, one after another."""
    r = read_varint(p)
    if r is None:
        return None, WHY_R_SIZE_ENDS
    hsize, n = r
    if hsize < n:
        return None, WHY_R_SIZE_SMALL
    if hsize > len(p):
        return None, WHY_R_SIZE_PAST
    types, pos = [], n
    while pos < hsize:
        r = read_varint(p, pos, hsize)
        if r is None:
            return None, WHY_R_TYPE_PAST
        types.append(r[0])
        pos += r[1]
    if not types:
        return None, WHY_R_NO_COLUMN
    values, body = [], hsize
    for t in types:
        size = content_size(t)
        if size is None:
            return None, WHY_R_RESERVED
        if body + size > len(p):
            return None, WHY_R_SHORT
        values.append(value_of(t, p[body:body + size]))
        body += size
    if body != len(p):
        return None, WHY_R_LONG
    return values, None


def opt(x):
    return "-" if x is None else str(x)


def show_header(h):
    return " ".join(str(x) for x in h)


def show_cell(p, c):
    left, size, rowid, kept, overflow = c
    return f"{p}/{opt(left)}/{opt(size)}/{opt(rowid)}/{hx(kept)}/{opt(overflow)}"


def show_page(pg):
    t, first_freeblock, count, content, fragmented, right, pointers, cells = pg
    return (f"{t} {first_freeblock} {count} {content} {fragmented} {opt(right)} |"
            + "".join(" " + show_cell(p, c) for p, c in zip(pointers, cells)))


WHY_V_ENDS = "the varint does not end (1.6)"


def model(op, args):
    """The model's answer to a request, and why it is FAIL (or None)."""
    if op == "varint":
        r = read_varint(args[0])
        if r is None:
            return "FAIL", WHY_V_ENDS
        return f"OK {r[0]} {r[1]} {hx(args[0][r[1]:])}", None
    if op == "header":
        h, why = read_header(args[0])
        return ("FAIL", why) if h is None else ("OK " + show_header(h), None)
    if op == "page":
        n, f = args
        h, why = read_header(f)
        if h is None:
            return "FAIL", WHY_P_HEADER
        pg, why = read_page(h, f, n)
        return ("FAIL", why) if pg is None else ("OK " + show_page(pg), None)
    if op == "record":
        vs, why = read_record(args[0])
        return ("FAIL", why) if vs is None else ("OK " + " ".join(vs), None)
    if op == "local":
        t, U, P = args
        return f"OK {local_size(t, U, P)}", None
    raise ValueError(op)


def request(op, args):
    if op == "page":
        return f"page {args[0]} {hx(args[1])}"
    if op == "local":
        return f"local {args[0]} {args[1]} {args[2]}"
    return f"{op} {hx(args[0])}"


def model_dump(f):
    """What `sqlite dump` prints for the file f, as lines, and its exit
    status: the header, then each whole page in turn, read or FAIL, and
    the record of each cell whose payload is all on its page."""
    h, _ = read_header(f)
    if h is None:
        return [], 1
    out = ["header " + show_header(h)]
    ps = h[H_PAGE_SIZE]
    for n in range(1, len(f) // ps + 1):
        pg, _ = read_page(h, f, n)
        if pg is None:
            out.append(f"page {n} FAIL")
            continue
        out.append(f"page {n} {show_page(pg)}")
        for p, c in zip(pg[6], pg[7]):
            if c[4] is None and c[3]:
                vs, _ = read_record(c[3])
                out.append(f"record {n} {p} {opt(c[2])} " + ("FAIL" if vs is None else " ".join(vs)))
    return out, 0


HEX_DIGITS = frozenset("0123456789abcdef")
DIGITS = frozenset("0123456789")


def hex_field(f):
    if f == "-":
        return b""
    if not f or len(f) % 2 or any(c not in HEX_DIGITS for c in f):
        return None
    return bytes.fromhex(f)


def decimal_field(f):
    if not f or any(c not in DIGITS for c in f):
        return None
    return int(f)


def parse_request(line):
    """The operation and arguments of a request line, or None when it is
    malformed."""
    fs = line.split(" ")
    op = fs[0]
    if op in ("varint", "header", "record") and len(fs) == 2:
        b = hex_field(fs[1])
        return None if b is None else (op, [b])
    if op == "page" and len(fs) == 3:
        n, b = decimal_field(fs[1]), hex_field(fs[2])
        return None if n is None or b is None else (op, [n, b])
    if op == "local" and len(fs) == 4:
        t, U, P = (decimal_field(x) for x in fs[1:])
        if t not in PAGE_TYPES or U is None or P is None:
            return None
        return (op, [t, U, P])
    return None


def model_line(raw):
    """What the tool must answer to a request line, malformed or not."""
    line = raw[:-1] if raw.endswith("\n") else raw
    if raw.endswith("\n") and line.endswith("\r"):
        line = line[:-1]
    req = parse_request(line)
    return "error" if req is None else model(*req)[0]


# ---------------------------------------------------------------------
# Spec.lean's `examples` and `rejects`, with the answers they state.

# Spec/Examples.lean `sqliteHeaderBytes`: the first 100 bytes of a
# database SQLite 3.45.1 wrote.
SPEC_HEADER = bytes([
    0x53, 0x51, 0x4C, 0x69, 0x74, 0x65, 0x20, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x20, 0x33, 0x00,
    0x02, 0x00, 0x01, 0x01, 0x00, 0x40, 0x20, 0x20, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x04,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
    0x00, 0x2E, 0x76, 0x89])
# `onePageFile`: that header, then a table leaf page with one cell at 507.
ONE_PAGE_FILE = (SPEC_HEADER + bytes([0x0D, 0, 0, 0, 1, 1, 0xFB, 0, 1, 0xFB]) + bytes(397)
                 + bytes([3, 1, 2, 1, 5]))


def spec_header_with(**changes):
    """`headerBytes { sqliteHeader with ... }`."""
    b = bytearray(SPEC_HEADER)
    for k, v in changes.items():
        if k == "pageSize":
            b[16:18] = (1 if v == 65536 else v).to_bytes(2, "big")
        elif k == "readVersion":
            b[19] = v
        elif k == "reserved":
            b[20] = v
        elif k == "textEncoding":
            b[56:60] = v.to_bytes(4, "big")
    return bytes(b)


SPEC_CASES = [
    # examples
    ("varint", [b"\x00"], "OK 0 1 -"),
    ("varint", [b"\x7f\x55"], "OK 127 1 55"),
    ("varint", [b"\x81\x00"], "OK 128 2 -"),
    ("varint", [b"\xff" * 9], f"OK {2 ** 64 - 1} 9 -"),
    ("local", [TABLE_LEAF, 4096, 10000], "OK 1816"),
    ("record", [bytes([3, 1, 0x13, 7, 0x61, 0x62, 0x63])], "OK int:7 text:616263"),
    ("header", [SPEC_HEADER], "OK 512 1 1 0 2 3 0 0 1 4 0 0 1 0 0 0 2 3045001"),
    ("page", [1, ONE_PAGE_FILE], "OK 13 0 1 507 0 - | 507/-/3/1/020105/-"),
    ("record", [bytes([2, 1, 5])], "OK int:5"),
    # rejects
    ("varint", [b"\x81\x80"], "FAIL"),
    ("header", [bytes(16) + SPEC_HEADER[16:]], "FAIL"),
    ("header", [spec_header_with(pageSize=768)], "FAIL"),
    ("header", [spec_header_with(readVersion=3)], "FAIL"),
    ("header", [spec_header_with(reserved=33)], "FAIL"),
    ("header", [spec_header_with(textEncoding=0)], "FAIL"),
    ("header", [SPEC_HEADER[:21] + bytes([63]) + SPEC_HEADER[22:]], "FAIL"),
    ("page", [2, ONE_PAGE_FILE], "FAIL"),
    ("page", [0, ONE_PAGE_FILE], "FAIL"),
    ("record", [bytes([2, 0x0A])], "FAIL"),
    ("record", [bytes([2, 1, 7, 0])], "FAIL"),
    ("record", [bytes([5, 1])], "FAIL"),
    ("record", [bytes([1])], "FAIL"),
]

# ---------------------------------------------------------------------
# Encoders, for building inputs.


def varint_len(v):
    for k in range(1, 9):
        if v < 1 << (7 * k):
            return k
    return 9


def enc_varint(v, length=None):
    """v (below 2^64) as a varint of `length` bytes, the fewest when
    None; a varint of fewer than 9 bytes holds 7 bits a byte."""
    length = varint_len(v) if length is None else length
    if length == 9:
        a = v >> 8
        return bytes(((a >> (7 * (7 - i))) & 0x7F) | 0x80 for i in range(8)) + bytes([v & 0xFF])
    assert v < 1 << (7 * length)
    return bytes(((v >> (7 * (length - 1 - i))) & 0x7F) | (0x80 if i < length - 1 else 0)
                 for i in range(length))


def some_varint(rng, v):
    """v as a varint, mostly in the fewest bytes, sometimes in more."""
    k = varint_len(v)
    if k < 9 and rng.random() < 0.15:
        k = rng.randint(k, 9)
    return enc_varint(v, k)


INT_EDGES = sorted({s * (2 ** k + d) for k in (0, 7, 8, 15, 16, 23, 24, 31, 32, 47, 48, 53, 63)
                    for d in (-1, 0, 1) for s in (1, -1)
                    if -2 ** 63 <= s * (2 ** k + d) < 2 ** 63} | {0, 1, 2, -2})
INT_WIDTH = {1: 1, 2: 2, 3: 3, 4: 4, 5: 6, 6: 8}


def random_int(rng):
    if rng.random() < 0.4:
        return rng.choice(INT_EDGES)
    bits = rng.randint(0, 63)
    v = rng.getrandbits(bits) if bits else 0
    return -v - 1 if rng.random() < 0.5 else v


def int_type(v, rng=None):
    """The serial type for v in the fewest bytes, or, with rng,
    sometimes a wider one."""
    for t in range(1, 7):
        if -(1 << (8 * INT_WIDTH[t] - 1)) <= v < 1 << (8 * INT_WIDTH[t] - 1):
            if rng is not None and rng.random() < 0.15:
                return rng.randint(t, 6)
            return t
    raise ValueError(v)


def blob_size(rng):
    r = rng.random()
    if r < 0.6:
        return rng.randint(0, 20)
    if r < 0.94:
        return rng.randint(21, 150)
    if r < 0.999:
        return rng.randint(151, 3000)
    return rng.randint(3001, 70000)


def random_column(rng):
    """A serial type and content."""
    r = rng.random()
    if r < 0.08:
        return 0, b""
    if r < 0.45:
        v = random_int(rng)
        t = int_type(v, rng)
        return t, v.to_bytes(INT_WIDTH[t], "big", signed=True)
    if r < 0.52:
        return rng.choice((8, 9)), b""
    if r < 0.64:
        return 7, rng.choice([struct.pack(">d", x) for x in (0.0, -0.0, 1.0, 1.5, -2.25, 1e300,
                                                              5e-324, float("inf"))]
                             + [rng.randbytes(8)] * 4)
    n = blob_size(rng)
    return (12 if r < 0.82 else 13) + 2 * n, rng.randbytes(n)


def record_bytes(rng, cols, header_len=None):
    """A record of the columns (serial type, content)."""
    types = b"".join(some_varint(rng, t) for t, _ in cols)
    body = b"".join(c for _, c in cols)
    k = 1
    while varint_len(k + len(types)) > k:
        k += 1
    if header_len is not None:
        k = max(k, header_len)
    elif k < 9 and rng.random() < 0.08:
        k = rng.randint(k, 9)
    return enc_varint(k + len(types), k) + types + body


# ---------------------------------------------------------------------
# Inputs that are not databases. Each item is (label, op, args).


def varint_sets(rng):
    for x in range(256):
        yield ("every varint of one byte", "varint", [bytes([x])])
    for x in range(65536):
        yield ("every two bytes", "varint", [x.to_bytes(2, "big")])
    for k in range(1, 10):
        for v in (0, 1, 127, 128, (1 << (7 * k)) - 1, 1 << (7 * k), 2 ** 63, 2 ** 64 - 1):
            if v < 2 ** 64 and varint_len(v) <= k:
                yield ("each length, at its bounds", "varint", [enc_varint(v, k)])
                yield ("each length, at its bounds, with bytes after", "varint",
                       [enc_varint(v, k) + rng.randbytes(rng.randint(1, 4))])
                yield ("each length, at its bounds, cut short", "varint", [enc_varint(v, k)[:-1]])
    for last in range(256):
        yield ("nine bytes, every ninth byte", "varint", [rng.randbytes(8) + bytes([last])])
        yield ("nine bytes, every ninth byte", "varint",
               [bytes(x | 0x80 for x in rng.randbytes(8)) + bytes([last])])


def random_varint(rng):
    k = rng.randint(0, 12)
    b = bytearray(rng.randbytes(k))
    for i in range(min(k, rng.randint(0, 10))):
        b[i] |= 0x80
    return bytes(b)


def make_header(rng, page_size, reserved, **fields):
    """A header this reader accepts, with random fields."""
    words = {
        H_CHANGE: rng.getrandbits(32), H_SIZE: rng.getrandbits(rng.choice((4, 16, 32))),
        H_TRUNK: rng.getrandbits(rng.choice((0, 8, 32))), H_FREE: rng.getrandbits(rng.choice((0, 8, 32))),
        H_COOKIE: rng.getrandbits(32), H_SCHEMA: rng.randint(0, 4),
        H_CACHE: rng.getrandbits(32), H_LARGEST: rng.getrandbits(rng.choice((0, 8, 32))),
        H_ENCODING: rng.randint(1, 3), H_USER: rng.getrandbits(32),
        H_INCREMENTAL: rng.getrandbits(rng.choice((0, 1, 32))), H_APPID: rng.getrandbits(32),
    }
    words.update(fields)
    b = bytearray(MAGIC)
    b += (1 if page_size == 65536 else page_size).to_bytes(2, "big")
    b += bytes([fields.get(H_WRITE, rng.choice((1, 2, 0, 3, 255))), fields.get(H_READ, rng.choice((1, 2))),
                reserved, 64, 32, 32])
    for i in range(H_CHANGE, H_APPID + 1):
        b += words[i].to_bytes(4, "big")
    b += bytes(20)
    b += rng.getrandbits(32).to_bytes(4, "big") + rng.getrandbits(32).to_bytes(4, "big")
    return bytes(b)


def random_reserved(rng, page_size):
    if rng.random() < 0.5:
        return 0
    return rng.randint(1, min(255, page_size - 480))


def random_header(rng):
    """A header from random fields, each mostly one this reader accepts."""
    ps = rng.choice(PAGE_SIZES)
    b = bytearray(make_header(rng, ps, random_reserved(rng, ps)))
    for _ in range(rng.choice((0, 1, 1, 2, 3))):
        what = rng.randrange(9)
        if what == 0:
            b[rng.randrange(16)] = rng.randrange(256)
        elif what == 1:
            b[16:18] = rng.choice((0, 1, 2, 256, 511, 513, 768, 32768, 65535, rng.getrandbits(16),
                                   rng.choice(PAGE_SIZES[:-1]))).to_bytes(2, "big")
        elif what == 2:
            b[18 + rng.randrange(2)] = rng.choice((0, 1, 2, 3, 255, rng.randrange(256)))
        elif what == 3:
            b[20] = rng.randrange(256)
        elif what == 4:
            b[21 + rng.randrange(3)] = rng.choice((0, 31, 32, 33, 63, 64, 65, rng.randrange(256)))
        elif what == 5:
            b[44:48] = rng.choice((0, 4, 5, 2 ** 32 - 1, rng.getrandbits(32))).to_bytes(4, "big")
        elif what == 6:
            b[56:60] = rng.choice((0, 1, 3, 4, 2 ** 32 - 1, rng.getrandbits(32))).to_bytes(4, "big")
        elif what == 7:
            b[72 + rng.randrange(20)] = rng.randrange(1, 256)
        else:
            b[rng.randrange(100)] = rng.randrange(256)
    return bytes(b) + rng.randbytes(rng.choice((0, 0, 1, 50)))


def random_record(rng):
    n = rng.choice((1, 1, 2, 3, 4, 6, 10)) if rng.random() < 0.98 else rng.randint(11, 80)
    cols = [random_column(rng) for _ in range(n)]
    return cols, record_bytes(rng, cols)


def changed_record(rng, cols, rec):
    """The record changed in one way; a label and the bytes."""
    what = rng.randrange(12)
    if what == 0:
        i = rng.randrange(len(cols))
        cols = cols[:i] + [(rng.choice((10, 11)), cols[i][1])] + cols[i + 1:]
        return "serial type 10 or 11", record_bytes(rng, cols)
    if what == 1:
        i = rng.randrange(len(cols))
        t = rng.choice((2 ** 64 - 1, 2 ** 64 - 2, 2 ** 63, rng.getrandbits(64), 2 * len(rec) + 12,
                        2 * len(rec) + 13))
        cols = cols[:i] + [(t, cols[i][1])] + cols[i + 1:]
        return "a huge serial type", record_bytes(rng, cols)
    if what == 2:
        return "the body one byte longer", rec + rng.randbytes(1)
    if what == 3:
        return "the body one byte shorter", rec[:-1]
    if what == 4:
        return "no body", record_bytes(rng, [(t, b"") for t, _ in cols])
    r = read_varint(rec)
    hsize, k = r
    rest = rec[k:]
    if what == 5:
        return "the header size one more", enc_varint(hsize + 1, k if varint_len(hsize + 1) <= k else None) + rest
    if what == 6:
        return "the header size one less", enc_varint(hsize - 1, k) + rest
    if what == 7:
        small = rng.randrange(0, 2)
        return "a header size smaller than its varint", enc_varint(small, rng.randint(2, 9)) + rest
    if what == 8:
        return "a header size past the record", enc_varint(len(rec) + rng.randint(1, 300)) + rest
    if what == 9:
        return "a serial type running past the header", enc_varint(hsize, k) + rest[:hsize - k - 1] + bytes(
            [rec[hsize - 1] | 0x80]) + rest[hsize - k:]
    if what == 10:
        return "no column", bytes([1]) + rng.randbytes(rng.choice((0, 0, 1, 3)))
    b = bytearray(rec)
    b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    return "a bit flipped", bytes(b)


def local_sets(rng):
    us = list(range(0, 41)) + list(range(470, 530))
    us += [ps - r for ps in PAGE_SIZES for r in (0, 1, 2, 3, 8, 12, 17, 32, 33, 64, 100, 128, 200, 255)
           if ps - r >= 0]
    us += [65537, 2 ** 20, 2 ** 32 + 5, 10 ** 20]
    for U in sorted(set(us)):
        for t in PAGE_TYPES:
            X, M = max_local(t, U), min_local(U)
            ps = {0, 1, 2, U, 2 * U, 10 ** 25, 2 ** 64 - 1}
            for d in range(-3, 4):
                ps |= {X + d, M + d}
                for j in (1, 2, 3):
                    ps |= {X + j * nsub(U, 4) + d, M + j * nsub(U, 4) + d,
                           X + j * nsub(U, 4) + (X - M) + d}
            for _ in range(4):
                ps.add(rng.randrange(4 * U + 10))
            for P in sorted(p for p in ps if p >= 0):
                yield ("a grid of usable and payload sizes", "local", [t, U, P])
    for U in (480, 512):
        for t in PAGE_TYPES:
            for P in range(0, 3 * U + 1):
                yield ("every payload size up to three pages", "local", [t, U, P])


def random_local(rng):
    U = rng.choice((rng.randrange(480, 65537), rng.randrange(0, 600), rng.getrandbits(rng.randint(1, 40))))
    P = rng.choice((rng.randrange(0, 4 * U + 10), rng.getrandbits(rng.randint(1, 64))))
    return [rng.choice(PAGE_TYPES), U, P]


# ---------------------------------------------------------------------
# Built b-tree pages.


def random_key(rng):
    if rng.random() < 0.3:
        return rng.choice((0, 1, 2 ** 63 - 1, 2 ** 63, 2 ** 64 - 1, 2 ** 63 + 1, 127, 128))
    return rng.getrandbits(rng.choice((7, 14, 32, 63, 64)))


def payload_size(rng, t, U):
    """A payload size, often near X, M or K."""
    X, M, W = max_local(t, U), min_local(U), U - 4
    choices = [rng.randint(0, 40), X - rng.randint(0, 3), X + rng.randint(1, 3), M + rng.randint(-2, 2),
               X + rng.randint(1, 3) * W + rng.randint(-2, 2),
               M + rng.randint(1, 3) * W + rng.randint(-2, 2),
               X + rng.randint(1, 3) * W + (X - M) + rng.randint(-2, 2),
               rng.randint(0, 4 * U), rng.getrandbits(rng.choice((16, 32, 64)))]
    return min(max(0, rng.choice(choices)), 2 ** 64 - 1)


def random_cell(rng, t, U):
    """A cell of type t for usable size U, as bytes, and the bytes of its
    payload kept on the page, a record when one fits."""
    if t == TABLE_INTERIOR:
        return rng.getrandbits(32).to_bytes(4, "big") + some_varint(rng, random_key(rng))
    P = payload_size(rng, t, U)
    L = local_size(t, U, P)
    kept = rng.randbytes(L)
    if L == P and rng.random() < 0.5:
        cols, rec = random_record(rng)
        if len(rec) <= max_local(t, U):
            P = L = len(rec)
            kept = rec
    out = rng.getrandbits(32).to_bytes(4, "big") if t == INDEX_INTERIOR else b""
    out += some_varint(rng, P)
    if t == TABLE_LEAF:
        out += some_varint(rng, random_key(rng))
    out += kept
    if L < P:
        out += rng.getrandbits(32).to_bytes(4, "big")
    return out


def page_file(rng, ps, reserved, n, t, content, cells, count=None):
    """A file whose page n (1 or 2) has type t, the content start
    `content` and the cells [(offset, bytes)], pointers in order."""
    off = 100 if n == 1 else 0
    hs = 12 if t in INTERIOR else 8
    page = bytearray(ps)
    for p, c in cells:
        page[p:p + len(c)] = c[:ps - p]
    page[off] = t
    page[off + 3:off + 5] = (len(cells) if count is None else count).to_bytes(2, "big")
    page[off + 5:off + 7] = (content % 65536).to_bytes(2, "big")
    if t in INTERIOR:
        page[off + 8:off + 12] = rng.getrandbits(32).to_bytes(4, "big")
    for i, (p, _) in enumerate(cells):
        page[off + hs + 2 * i:off + hs + 2 * i + 2] = p.to_bytes(2, "big")
    header = make_header(rng, ps, reserved)
    if n == 1:
        page[:100] = header
        return bytes(page)
    return header + bytes(ps - 100) + bytes(page)


def edge_pages(rng):
    """Pages at the edges of PageEncodes: empty pages whose content
    start is just inside or outside the usable size, or 0; one cell that
    ends just inside or outside the usable size, or starts just before
    the content area; a content start just before, at and after the end
    of the pointer array."""
    for ps, reserved in ((512, 0), (512, 5), (4096, 0), (4096, 5), (65536, 0), (65536, 5)):
        U = ps - reserved
        for n in ((1,) if ps == 65536 else (1, 2)):
            off = 100 if n == 1 else 0
            for t in PAGE_TYPES:
                hs = 12 if t in INTERIOR else 8
                for content in sorted({U - 1, U, U + 1, ps, 65536}):
                    if content <= 65536:
                        yield ("an edge of a page, empty, content start U-1 to 65536", "page",
                               [n, page_file(rng, ps, reserved, n, t, content, [])])
                c = random_cell(rng, t, U)
                for end in (U - 1, U, U + 1):
                    p = end - len(c)
                    if p >= off + hs + 2 and end <= ps:
                        yield ("an edge of a page, a cell ending at U-1, U or U+1", "page",
                               [n, page_file(rng, ps, reserved, n, t, p, [(p, c)])])
                        yield ("an edge of a page, a cell starting one byte before the content area",
                               "page", [n, page_file(rng, ps, reserved, n, t, p + 1, [(p, c)])])
                p = U - len(c)
                floor = off + hs + 2
                for content in (floor - 1, floor, floor + 1):
                    if p >= floor + 1:
                        yield ("an edge of a page, a content start around the end of the pointer array",
                               "page", [n, page_file(rng, ps, reserved, n, t, content, [(p, c)])])
                    yield ("an edge of a page, a content start around the end of the pointer array",
                           "page", [n, page_file(rng, ps, reserved, n, t, content + 2, [], count=1)])


PAGE_DEFECTS = ["none"] * 6 + [
    "the content start past the first cell", "the content start before the pointer array ends",
    "the content start past the usable size", "the content start 0", "a cell pointer before the content area",
    "a cell running past the usable size", "the cell count one more", "the cell count one less",
    "a payload size one more", "a byte changed", "the page type changed"]


def built_page(rng, ps, reserved, n):
    """A file whose page n (1 or 2) is a b-tree page built from random
    parts, and the defect it was given."""
    U = ps - reserved
    off = 100 if n == 1 else 0
    t = rng.choice(PAGE_TYPES) if rng.random() < 0.97 else rng.randrange(256)
    tt = t if t in PAGE_TYPES else TABLE_LEAF
    hs = 12 if tt in INTERIOR else 8
    want = rng.choice((0, 0, 1, 2, 3, 5, 10, 30, 100))
    cells, pos = [], U
    for _ in range(want):
        c = random_cell(rng, tt, U)
        gap = rng.choice((0, 0, 0, 1, 3, 4, 10))
        if pos - gap - len(c) < off + hs + 2 * (len(cells) + 1):
            break
        pos -= gap + len(c)
        cells.append((pos, c))
    floor = off + hs + 2 * len(cells)
    content = pos if rng.random() < 0.8 else rng.randint(floor, pos)
    page = bytearray(rng.randbytes(ps) if rng.random() < 0.5 else bytes(ps))
    pointers = [p for p, _ in cells]
    if rng.random() < 0.3:
        rng.shuffle(pointers)
    count = len(pointers)
    defect = rng.choice(PAGE_DEFECTS)
    if defect == "the content start past the first cell" and cells:
        content = min(pointers) + 1
    elif defect == "the content start before the pointer array ends":
        content = max(1, floor - 1)
    elif defect == "the content start past the usable size":
        content = U + rng.randint(1, 3)
    elif defect == "the content start 0":
        content = 65536
    elif defect == "a cell pointer before the content area" and cells:
        pointers[rng.randrange(count)] = max(0, content - rng.randint(1, 4))
    elif defect == "a cell running past the usable size" and cells:
        i = rng.randrange(count)
        c = dict((p, c) for p, c in cells)[pointers[i]]
        p = U - len(c) + rng.randint(1, 4)
        if p + len(c) <= ps:
            page[p:p + len(c)] = c
        pointers[i] = p
    elif defect == "the cell count one more":
        count += 1
    elif defect == "the cell count one less" and count:
        count -= 1
    else:
        defect = defect if defect in ("none", "a payload size one more", "a byte changed",
                                      "the page type changed") else "none"
    for p, c in cells:
        page[p:p + len(c)] = c
    if defect == "a payload size one more" and cells and tt != TABLE_INTERIOR:
        p, c = rng.choice(cells)
        q = p + (4 if tt == INDEX_INTERIOR else 0)
        r = read_varint(page, q)
        if r and r[0] + 1 < 2 ** 64 and varint_len(r[0] + 1) <= r[1]:
            page[q:q + r[1]] = enc_varint(r[0] + 1, r[1])
    page[off] = t
    page[off + 1:off + 3] = rng.choice((0, rng.getrandbits(16))).to_bytes(2, "big")
    page[off + 3:off + 5] = min(count, 65535).to_bytes(2, "big")
    page[off + 5:off + 7] = (content % 65536 if content <= 65536 else content % 65536).to_bytes(2, "big")
    page[off + 7] = rng.choice((0, rng.randrange(256)))
    if tt in INTERIOR:
        page[off + 8:off + 12] = rng.getrandbits(32).to_bytes(4, "big")
    for i, p in enumerate(pointers[:count] + [rng.getrandbits(16)] * (count - len(pointers))):
        page[off + hs + 2 * i:off + hs + 2 * i + 2] = (p % 65536).to_bytes(2, "big")
    if defect == "a byte changed":
        page[rng.randrange(off, ps)] = rng.randrange(256)
    elif defect == "the page type changed":
        page[off] = {2: 10, 10: 2, 5: 13, 13: 5}.get(t, rng.choice(PAGE_TYPES))
    header = make_header(rng, ps, reserved)
    if n == 1:
        page[:100] = header
        return bytes(page), defect
    return header + bytes(ps - 100) + bytes(page), defect


# ---------------------------------------------------------------------
# Pages of real databases, changed.

INTERESTING_16 = (0, 1, 2, 7, 8, 12, 99, 100, 107, 108, 112, 255, 256, 479, 480, 511, 512, 513,
                  1023, 1024, 4095, 4096, 32767, 32768, 65534, 65535)


def changed_page(rng, h, f, n):
    """f, a file with header h, with page n changed in one way; the label
    and the bytes."""
    ps, U = h[H_PAGE_SIZE], h[H_PAGE_SIZE] - h[H_RESERVED]
    base = (n - 1) * ps
    off = base + (100 if n == 1 else 0)
    b = bytearray(f)
    pg, _ = read_page(h, f, n)
    t = b[off]
    hs = 12 if t in INTERIOR else 8
    count = be(b[off + 3:off + 5])
    kinds = ["a bit flipped", "a page header byte changed", "the cell count changed",
             "the content start changed", "the page type changed", "the reserved byte of the header changed",
             "the page size field changed", "the file cut short", "the freeblock and fragment fields changed"]
    if count:
        kinds.append("a cell pointer changed")
    if pg is not None and pg[2]:
        kinds.append("a byte of a cell changed")
        if t != TABLE_INTERIOR:
            kinds += ["a payload size changed"] * 2
        if t in (TABLE_LEAF, TABLE_INTERIOR):
            kinds.append("a rowid changed")
        if any(c[4] is not None for c in pg[7]):
            kinds.append("an overflow page number changed")
    if pg is not None and t in INTERIOR:
        kinds.append("the right-most pointer changed")
    what = rng.choice(kinds)
    if what == "a page header byte changed":
        b[off + rng.randrange(hs)] = rng.choice((0, 1, 2, 5, 10, 13, 255, rng.randrange(256)))
    elif what == "the cell count changed":
        b[off + 3:off + 5] = max(0, min(65535, count + rng.choice((-2, -1, 1, 2, 100, 65535)))).to_bytes(2, "big")
    elif what == "the content start changed":
        cs = be(b[off + 5:off + 7]) or 65536
        floor = (off - base) + hs + 2 * count
        new = rng.choice((0, 1, floor - 1, floor, floor + 1, cs - 1, cs + 1, U - 1, U, U + 1,
                          rng.choice(INTERESTING_16)))
        b[off + 5:off + 7] = (max(0, new) % 65536).to_bytes(2, "big")
    elif what == "a cell pointer changed":
        i = rng.randrange(min(count, (ps - (off - base) - hs) // 2))
        cs = be(b[off + 5:off + 7]) or 65536
        new = rng.choice((cs - 1, cs, U - 1, U - 4, U, ps - 1, rng.choice(INTERESTING_16), rng.randrange(ps)))
        b[off + hs + 2 * i:off + hs + 2 * i + 2] = (max(0, new) % 65536).to_bytes(2, "big")
    elif what == "a payload size changed":
        q = base + rng.choice(pg[6]) + (4 if t == INDEX_INTERIOR else 0)
        r = read_varint(b, q)
        P = payload_size(rng, t, U)
        if varint_len(P) > r[1]:
            P = rng.getrandbits(7 * r[1]) if r[1] < 9 else rng.getrandbits(64)
        b[q:q + r[1]] = enc_varint(P, r[1])
    elif what == "a rowid changed":
        i = rng.randrange(pg[2])
        q = base + pg[6][i] + 4
        if t == TABLE_LEAF:
            q = base + pg[6][i] + read_varint(b, base + pg[6][i])[1]
        r = read_varint(b, q)
        v = rng.getrandbits(64) if r[1] == 9 else rng.getrandbits(7 * r[1])
        b[q:q + r[1]] = enc_varint(v, r[1])
    elif what == "the page type changed":
        b[off] = rng.choice([x for x in PAGE_TYPES if x != t] + [0, 1, 255])
    elif what == "a byte of a cell changed":
        p = base + rng.choice(pg[6]) + rng.randrange(6)
        if p < base + ps:
            b[p] = rng.randrange(256)
    elif what == "an overflow page number changed":
        i = rng.choice([k for k, c in enumerate(pg[7]) if c[4] is not None])
        c, _ = read_cell(t, U, f[base:base + ps], pg[6][i])
        _, size = read_cell(t, U, f[base:base + ps], pg[6][i])
        p = base + pg[6][i] + size - 4
        b[p:p + 4] = rng.getrandbits(32).to_bytes(4, "big")
    elif what == "the reserved byte of the header changed":
        b[20] = min(255, rng.choice((0, 1, h[H_RESERVED] + 1, h[H_RESERVED] + 4, ps - 480, ps - 479,
                                     rng.randrange(256))))
    elif what == "the page size field changed":
        new = rng.choice(PAGE_SIZES)
        b[16:18] = (1 if new == 65536 else new).to_bytes(2, "big")
    elif what == "the file cut short":
        del b[len(b) - rng.randint(1, 8):]
    elif what == "the right-most pointer changed":
        b[off + 8:off + 12] = rng.getrandbits(32).to_bytes(4, "big")
    elif what == "the freeblock and fragment fields changed":
        b[off + 1:off + 3] = rng.choice((0, rng.getrandbits(16))).to_bytes(2, "big")
        b[off + 7] = rng.randrange(256)
    else:
        b[base + rng.randrange(ps)] ^= 1 << rng.randrange(8)
    return what, bytes(b)


# ---------------------------------------------------------------------
# Databases made by SQLite.

TEXT_POOL = "abcdefghij ABC 0123456789 _-.,;\x00\n\té€üßøñ日本語中文한국😀🎉 "
DECLS = ["", "", "INTEGER", "INT", "REAL", "DOUBLE", "FLOAT", "TEXT", "VARCHAR(20)", "BLOB", "NUMERIC",
         "BOOLEAN", "DATE"]
STRICT_DECLS = ["INT", "INTEGER", "REAL", "TEXT", "BLOB", "ANY"]
FLOAT_EDGES = [0.0, -0.0, 1.0, -1.0, 0.5, 3.0, -7.0, 1e15, 2.0 ** 53, 2.0 ** 63, -(2.0 ** 63), 1e300, -1e-300,
               5e-324, float("inf"), float("-inf"), float("nan"), 123456789.0, 0.1]


def affinity(decl):
    """The affinity of a declared type (datatype3.html 3.1)."""
    d = decl.upper()
    if "INT" in d:
        return "INTEGER"
    if "CHAR" in d or "CLOB" in d or "TEXT" in d:
        return "TEXT"
    if "BLOB" in d or not d:
        return "BLOB"
    if "REAL" in d or "FLOA" in d or "DOUB" in d:
        return "REAL"
    return "NUMERIC"


def value_bytes(rng, big, share):
    """The size of a text or blob: mostly small, and, when `big` is
    positive, a share of them up to `big` bytes; at most -big bytes when
    it is negative."""
    if big < 0:
        return rng.randint(0, -big)
    if big and rng.random() < share:
        return rng.randint(1000, big)
    r = rng.random()
    if r < 0.6:
        return rng.randint(0, 24)
    if r < 0.92:
        return rng.randint(25, 400)
    return rng.randint(401, 3000)


def sql_value(rng, kind, s):
    if kind == "null":
        return None
    if kind == "int":
        return random_int(rng)
    if kind == "bool":
        return rng.randint(0, 1)
    if kind == "real":
        if rng.random() < 0.4:
            return rng.choice(FLOAT_EDGES)
        x = struct.unpack(">d", rng.randbytes(8))[0]
        return 0.0 if x != x else x
    n = value_bytes(rng, s.big or 0, s.big_share or 0.04)
    if kind == "text":
        if n > 2000:
            return (rng.choice(TEXT_POOL) * n)[:n]
        return "".join(rng.choice(TEXT_POOL) for _ in range(n))
    return rng.randbytes(n)


KINDS = ("null", "int", "bool", "real", "text", "blob")
STRICT_KINDS = {"INT": ("null", "int", "bool"), "INTEGER": ("null", "int", "bool"),
                "REAL": ("null", "real", "int"), "TEXT": ("null", "text"), "BLOB": ("null", "blob"),
                "ANY": KINDS}


class Settings(dict):
    """Settings of a database; a setting not given is None."""
    __getattr__ = dict.get
    __setattr__ = dict.__setitem__


def table(cols, kind="rowid", pk=(), indexes=(), rows=None, strict=False):
    """A table of a fixed database: columns (declared type, value kinds),
    its kind (rowid, alias, pk or without), primary key columns, and
    indexes (lists of column numbers)."""
    return dict(cols=cols, kind=kind, pk=list(pk), indexes=[list(x) for x in indexes], rows=rows,
                strict=strict)


ANY = ("null", "int", "bool", "real", "text", "blob")

# The fixed databases: what each is for, and its settings. `rows` is an
# upper bound: rows go in until the file reaches its budget (see
# `budget`).
FIXED_DATABASES = [
    ("4096-byte pages, as SQLite makes them by default",
     Settings(page_size=4096, tables=3, rows=400, indexes=2)),
    ("65536-byte pages: an empty table, an empty index and an empty WITHOUT ROWID table, whose "
     "content start 0 means 65536; long overflow chains",
     Settings(page_size=65536, big=150000, big_share=0.25, schema=[
         table([("", ("int", "text")), ("BLOB", ("blob",))], indexes=[[0]], rows=0),
         table([("TEXT", ("text",)), ("", ANY)], kind="without", pk=[0], rows=0),
         table([("", ("blob", "text")), ("REAL", ("real", "int"))], indexes=[[1]], rows=60)])),
    ("512-byte pages: deep table and index trees, negative and huge rowids",
     Settings(page_size=512, rows=3000, rowids="wide", big=-30, schema=[
         table([("INTEGER", ("int",)), ("TEXT", ("text", "null"))], indexes=[[0], [1, 0]]),
         table([("", ANY), ("", ANY), ("", ANY)], kind="without", pk=[1, 0], indexes=[[2]])])),
    ("512-byte pages: payload sizes on both sides of X, M and K, in a table and an index",
     Settings(page_size=512, sweep=True)),
    ("1024-byte pages, 33 bytes reserved (a usable size of 991): payload sizes around X, M and K",
     Settings(page_size=1024, reserve=33, sweep=True)),
    ("2048-byte pages, 255 bytes reserved, big values over overflow chains",
     Settings(page_size=2048, reserve=255, tables=2, rows=200, big=30000, big_share=0.2, indexes=1)),
    ("65536-byte pages, 200 bytes reserved, long overflow chains",
     Settings(page_size=65536, reserve=200, tables=1, rows=40, big=300000, big_share=0.3)),
    ("UTF-16le text, WITHOUT ROWID tables",
     Settings(page_size=1024, encoding="UTF-16le", tables=3, rows=300, without=1.0, indexes=2)),
    ("UTF-16be text, auto_vacuum full, deletes",
     Settings(page_size=1024, encoding="UTF-16be", auto_vacuum=1, tables=3, rows=300, deletes=0.5,
              indexes=1)),
    ("incremental vacuum, WAL, deletes that leave free pages",
     Settings(page_size=1024, auto_vacuum=2, wal=True, tables=3, rows=400, deletes=0.6, drop=True,
              incremental=True, indexes=1)),
    ("secure_delete off: free pages keep the b-tree pages they were",
     Settings(page_size=512, secure_delete="OFF", tables=3, rows=400, deletes=0.6, updates=0.3, drop=True,
              indexes=1)),
    ("the legacy file format (schema format 1): 0 and 1 as serial type 1",
     Settings(page_size=1024, legacy=True, tables=2, rows=300, indexes=1, schema=[
         table([("", ("bool", "int")), ("", ("bool", "null"))], indexes=[[1]]),
         table([("BOOLEAN", ("bool",)), ("TEXT", ("text",))], kind="without", pk=[1])])),
    ("no table, only user_version, application_id and default_cache_size",
     Settings(page_size=4096, tables=0)),
    ("a table of 70 columns: record headers of more than 127 bytes",
     Settings(page_size=4096, wide=True, tables=1, rows=60)),
    ("8192-byte pages: index keys that spill, on interior and leaf index pages",
     Settings(page_size=8192, big=20000, big_share=0.4, schema=[
         table([("TEXT", ("text",)), ("", ("int",))], indexes=[[0]], rows=300),
         table([("BLOB", ("blob",)), ("", ANY)], kind="without", pk=[0], rows=200)])),
    ("STRICT tables with REAL columns holding whole numbers",
     Settings(page_size=2048, strict=1.0, tables=3, rows=300, indexes=1, schema=[
         table([("REAL", ("int", "real")), ("INTEGER", ("int",)), ("ANY", ANY)], indexes=[[0]],
               strict=True),
         table([("REAL", ("real", "int")), ("TEXT", ("text",))], kind="without", pk=[0], strict=True),
         table([("REAL", ("int",)), ("", ("real",))], indexes=[[0, 1]])])),
    ("AUTOINCREMENT, ANALYZE, views and triggers",
     Settings(page_size=1024, autoincrement=True, analyze=True, views=True, tables=3, rows=200,
              indexes=2)),
    ("512-byte pages, 40 tables: sqlite_schema spans pages, so page 1 is an interior page",
     Settings(page_size=512, tables=40, rows=3, indexes=1)),
    ("32768-byte pages, 1 byte reserved, VACUUM after deletes and updates",
     Settings(page_size=32768, reserve=1, tables=2, rows=800, deletes=0.4, updates=0.4, vacuum=True,
              indexes=1)),
    ("16384-byte pages, UTF-16be, auto_vacuum full, 7 bytes reserved, big text",
     Settings(page_size=16384, reserve=7, encoding="UTF-16be", auto_vacuum=1, tables=2, rows=300,
              big=40000, big_share=0.1, indexes=1, deletes=0.3)),
]


def random_settings(rng):
    ps = rng.choice(PAGE_SIZES[:5] * 3 + PAGE_SIZES[5:])
    return Settings(
        page_size=ps,
        reserve=random_reserved(rng, ps) if rng.random() < 0.3 else 0,
        encoding=rng.choice(("UTF-8",) * 4 + ("UTF-16le", "UTF-16be")),
        auto_vacuum=rng.choice((0, 0, 1, 2)), wal=rng.random() < 0.2, legacy=rng.random() < 0.1,
        secure_delete=rng.choice(("ON", "OFF", "FAST")),
        tables=rng.randint(1, 4), rows=rng.choice((5, 50, 200, 600)),
        big=rng.choice((0, 0, 5000, 50000)), big_share=rng.choice((0.02, 0.1)),
        indexes=rng.randint(0, 3), without=rng.choice((0, 0, 0.5)),
        strict=rng.choice((0, 0, 0.3)), deletes=rng.choice((0, 0, 0.3, 0.7)),
        updates=rng.choice((0, 0, 0.3)), drop=rng.random() < 0.2, vacuum=rng.random() < 0.15,
        incremental=rng.random() < 0.3, rowids=rng.choice(("auto", "auto", "wide")),
        autoincrement=rng.random() < 0.1, analyze=rng.random() < 0.1, views=rng.random() < 0.1,
        empty=rng.random() < 0.15, wide=rng.random() < 0.05,
        user_version=rng.choice((None, rng.randint(-2 ** 31, 2 ** 31 - 1))),
        application_id=rng.choice((None, rng.randint(-2 ** 31, 2 ** 31 - 1))),
        cache_size=rng.choice((None, None, rng.randint(1, 2 ** 31 - 1))))


def budget(ps):
    """The most bytes a database of page size ps gets: `sqlite dump`
    takes time in proportion to the pages times the file size, so the
    budget grows as the square root of the page size (512 KB for 512-byte
    pages, 5.8 MB for 65536-byte pages)."""
    return int(512 * 1024 * (ps / 512) ** 0.5)


class Lib:
    """The SQLite library Python's sqlite3 module uses, through ctypes,
    for the two settings SQL does not reach: the reserved bytes and the
    legacy file format."""
    RESERVE_BYTES = 38          # SQLITE_FILECONTROL_RESERVE_BYTES
    LEGACY_FILE_FORMAT = 1016   # SQLITE_DBCONFIG_LEGACY_FILE_FORMAT

    def __init__(self, folder):
        if (sys.implementation.name != "cpython" or sysconfig.get_config_var("Py_GIL_DISABLED")
                or ctypes.sizeof(ctypes.c_void_p) != 8):
            raise OSError("not a 64-bit CPython with the GIL")
        self.lib = ctypes.CDLL("libsqlite3.so.0")
        self.lib.sqlite3_libversion.restype = ctypes.c_char_p
        version = self.lib.sqlite3_libversion().decode()
        if version != sqlite3.sqlite_version:
            raise OSError(f"libsqlite3.so.0 is {version}, the sqlite3 module {sqlite3.sqlite_version}")
        self.lib.sqlite3_db_filename.restype = ctypes.c_char_p
        self.lib.sqlite3_db_filename.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
        self.lib.sqlite3_file_control.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_int,
                                                  ctypes.c_void_p]
        self.lib.sqlite3_db_config.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int,
                                               ctypes.c_void_p]
        probe = Path(folder) / "probe.db"
        con = sqlite3.connect(probe)
        try:
            self.handle(con, probe)
        finally:
            con.close()

    def handle(self, con, path):
        # The sqlite3* is the first field after the object header.
        h = ctypes.c_void_p.from_address(id(con) + 16).value
        name = self.lib.sqlite3_db_filename(h, b"main") if h else None
        if not name or os.path.realpath(name.decode()) != os.path.realpath(path):
            raise OSError("the connection's sqlite3 handle was not found")
        return h

    def configure(self, con, path, reserve, legacy):
        h = self.handle(con, path)
        if legacy and self.lib.sqlite3_db_config(h, self.LEGACY_FILE_FORMAT, 1, None) != 0:
            raise OSError("SQLITE_DBCONFIG_LEGACY_FILE_FORMAT failed")
        if reserve:
            v = ctypes.c_int(reserve)
            if self.lib.sqlite3_file_control(h, b"main", self.RESERVE_BYTES, ctypes.byref(v)) != 0:
                raise OSError("SQLITE_FILECONTROL_RESERVE_BYTES failed")


def q(name):
    return '"' + name.replace('"', '""') + '"'


def make_database(path, s, rng, lib):
    """Make a database at `path` with settings s; what the oracle needs
    to know about it that SQLite does not say (the partial indexes'
    conditions)."""
    con = sqlite3.connect(path, isolation_level=None)
    if lib is not None and (s.reserve or s.legacy):
        lib.configure(con, path, s.reserve, s.legacy)
    ex = con.execute
    ex(f"PRAGMA page_size = {s.page_size}")
    ex(f"PRAGMA encoding = '{s.encoding or 'UTF-8'}'")
    ex(f"PRAGMA auto_vacuum = {s.auto_vacuum or 0}")
    ex(f"PRAGMA secure_delete = {s.secure_delete or 'ON'}")
    if s.wal:
        ex("PRAGMA journal_mode = WAL")
    if s.user_version is not None:
        ex(f"PRAGMA user_version = {s.user_version}")
    if s.application_id is not None:
        ex(f"PRAGMA application_id = {s.application_id}")
    if s.cache_size is not None:
        ex(f"PRAGMA default_cache_size = {s.cache_size}")
    if not s.tables and not s.schema and not s.sweep:
        ex("PRAGMA user_version = 7")
        ex("PRAGMA application_id = -123456789")
        ex("PRAGMA default_cache_size = 1234")
    partial = {}
    tables = []
    ex("BEGIN")
    if s.sweep:
        sweep_tables(con, rng, s)
    specs = s.schema or [None] * (s.tables or 0)
    for ti, spec in enumerate(specs):
        tables.append(random_table(con, rng, s, ti, partial, spec))
    room = budget(s.page_size) // max(1, len(tables))
    for ti, t in enumerate(tables):
        n = t["rows"]
        if n is None:
            n = 0 if (s.empty and ti == 0) else max(1, int((s.rows or 50) * rng.uniform(0.5, 1.5)))
        insert_rows(con, rng, s, t, n, room * (ti + 1))
    ex("COMMIT")
    if s.deletes or s.updates:
        ex("BEGIN")
        for t in tables:
            change_rows(con, rng, s, t)
        ex("COMMIT")
    if s.drop and len(tables) > 1:
        ex(f"DROP TABLE {q(tables[-1]['name'])}")
        tables.pop()
    if s.views and tables:
        ex(f"CREATE VIEW v0 AS SELECT * FROM {q(tables[0]['name'])}")
        ex(f"CREATE TRIGGER g0 AFTER INSERT ON {q(tables[0]['name'])} BEGIN SELECT 1; END")
    if s.analyze:
        ex("ANALYZE")
    if s.incremental and s.auto_vacuum == 2:
        ex(f"PRAGMA incremental_vacuum({rng.randint(1, 5)})")
    if s.vacuum:
        ex("VACUUM")
    con.close()
    return {"partial": partial}


def sweep_tables(con, rng, s):
    """A table and an index whose payloads take every size near the
    places where the part kept on the page changes (1.6): X and X+1, and
    each time K wraps round, M+j*(U-4) and X+j*(U-4), for j up to 3."""
    U = s.page_size - (s.reserve or 0)
    con.execute("CREATE TABLE sweep_t (b)")
    con.execute("CREATE TABLE sweep_i (b)")
    con.execute("CREATE INDEX sweep_ix ON sweep_i (b)")
    for t, name in ((TABLE_LEAF, "sweep_t"), (INDEX_LEAF, "sweep_i")):
        X, M = max_local(t, U), min_local(U)
        marks = [X] + [M + j * (U - 4) for j in (1, 2, 3)] + [X + j * (U - 4) for j in (1, 2, 3)]
        sizes = sorted({max(0, m + d) for m in marks for d in range(-9, 8)})
        con.executemany(f"INSERT INTO {name} VALUES (?)", [(rng.randbytes(n),) for n in sizes])


def random_table(con, rng, s, ti, partial, spec):
    """Create a table, random where `spec` does not say, and its indexes.
    What the generator needs to know about it."""
    name = f"t{ti}"
    spec = spec or {}
    strict = spec.get("strict", rng.random() < (s.strict or 0))
    if "cols" in spec:
        decls = [d for d, _ in spec["cols"]]
        kinds = [k for _, k in spec["cols"]]
    else:
        ncols = 70 if s.wide else rng.choice((1, 2, 3, 4, 5, 8))
        decls = [rng.choice(STRICT_DECLS if strict else DECLS) for _ in range(ncols)]
        kinds = [tuple(rng.choice(STRICT_KINDS[d] if strict else KINDS) for _ in range(rng.randint(1, 4)))
                 for d in decls]
    cols = [f"c{i}" for i in range(len(decls))]
    if "kind" in spec:
        kind = spec["kind"]
    elif rng.random() < (s.without or 0):
        kind = "without"
    else:
        kind = rng.choice(("rowid", "rowid", "alias", "pk"))
    auto = s.autoincrement and ti == 0
    if auto:
        kind = "alias"
    defs = [f"{c} {d}".strip() for c, d in zip(cols, decls)]
    pk = []
    if kind == "alias":
        defs[0] = "c0 INTEGER PRIMARY KEY" + (" AUTOINCREMENT" if auto else "")
        # AUTOINCREMENT fails with SQLITE_FULL once the largest rowid is used.
        kinds[0] = ("null",) if auto else ("int", "null")
    elif kind in ("pk", "without"):
        pk = [cols[i] for i in spec["pk"]] if spec.get("pk") else \
            rng.sample(cols, min(len(cols), rng.choice((1, 1, 2))))
        for c in pk:
            i = cols.index(c)
            kinds[i] = tuple(k for k in kinds[i] if k != "null") or ("int",)
            if kind == "pk" and len(pk) == 1 and decls[i].upper() == "INTEGER":
                # PRIMARY KEY (c) of an INTEGER column would make c the rowid.
                decls[i] = "INT"
                defs[i] = f"{c} INT"
        defs.append("PRIMARY KEY (" + ", ".join(pk) + ")")
    if not spec and rng.random() < 0.2 and len(cols) > 1:
        defs.append(f"UNIQUE ({rng.choice(cols)})")
    options = (["WITHOUT ROWID"] if kind == "without" else []) + (["STRICT"] if strict else [])
    con.execute(f"CREATE TABLE {name} (" + ", ".join(defs) + ") " + ", ".join(options))
    if "indexes" in spec:
        index_cols = [[cols[i] for i in x] for x in spec["indexes"]]
    else:
        index_cols = [rng.sample(cols, min(len(cols), rng.randint(1, 3))) for _ in range(s.indexes or 0)]
    for xi, on in enumerate(index_cols):
        parts = []
        for c in on:
            part = c
            if rng.random() < 0.2:
                part += " COLLATE NOCASE"
            if rng.random() < 0.3:
                part += " DESC"
            parts.append(part)
        unique = "UNIQUE " if not spec and rng.random() < 0.15 else ""
        iname = f"i{ti}_{xi}"
        where = ""
        if rng.random() < 0.15:
            cond = f"{on[0]} IS NOT NULL" if rng.random() < 0.5 else f"typeof({on[0]}) = 'integer'"
            where = " WHERE " + cond
            partial[iname] = cond
        con.execute(f"CREATE {unique}INDEX {iname} ON {name} (" + ", ".join(parts) + ")" + where)
    return dict(name=name, cols=cols, kinds=kinds, kind=kind, pk=pk, rows=spec.get("rows"))


def insert_rows(con, rng, s, t, n, limit):
    """Insert up to n rows, in batches, until the file holds `limit`
    bytes."""
    name, cols, kinds, kind = t["name"], t["cols"], t["kinds"], t["kind"]
    explicit = kind != "without" and (s.rowids == "wide" or rng.random() < 0.3) and not (
        s.autoincrement and name == "t0")
    target = ["rowid"] + cols if explicit and kind != "alias" else cols
    sql = f"INSERT OR IGNORE INTO {name} (" + ", ".join(target) + ") VALUES (" + ", ".join(
        "?" * len(target)) + ")"
    done = 0
    while done < n:
        rows = []
        for _ in range(min(25, n - done)):
            vals = [sql_value(rng, rng.choice(k), s) for k in kinds]
            if kind == "alias" and explicit:
                vals[0] = random_rowid(rng, s)
            if explicit and kind != "alias":
                vals = [random_rowid(rng, s)] + vals
            rows.append(vals)
        con.executemany(sql, rows)
        done += len(rows)
        if con.execute("PRAGMA page_count").fetchone()[0] * s.page_size >= limit:
            break


def random_rowid(rng, s):
    if s.rowids == "wide" or rng.random() < 0.3:
        return rng.choice((rng.randint(-2 ** 63, 2 ** 63 - 1), rng.randint(-1000, 1000), 2 ** 63 - 1,
                           -2 ** 63, -1, 0, rng.randint(-2 ** 31, 2 ** 31)))
    return None


def change_rows(con, rng, s, t):
    name, cols, kinds, kind = t["name"], t["cols"], t["kinds"], t["kind"]
    if kind == "without":
        if s.deletes:
            con.execute(f"DELETE FROM {name} WHERE abs(random()) % 100 < {int(100 * s.deletes)}")
        return
    ids = [r[0] for r in con.execute(f"SELECT rowid FROM {name}")]
    gone = [i for i in ids if rng.random() < (s.deletes or 0)]
    con.executemany(f"DELETE FROM {name} WHERE rowid = ?", [(i,) for i in gone])
    gone = set(gone)
    for i in ids:
        if i not in gone and rng.random() < (s.updates or 0):
            c = rng.randrange(len(cols))
            if kind == "alias" and c == 0:
                continue
            con.execute(f"UPDATE OR IGNORE {name} SET {cols[c]} = ? WHERE rowid = ?",
                        (sql_value(rng, rng.choice(kinds[c]), s), i))


def all_databases(seed, count, lib):
    """The settings of every database to make: (label, settings, rng
    seed)."""
    rng = random.Random(seed * 7 + 3)
    out = []
    for label, s in FIXED_DATABASES:
        s = Settings(s)
        if lib is None and (s.reserve or s.legacy):
            s.reserve, s.legacy = 0, False
        out.append((label, s, rng.getrandbits(64)))
    for _ in range(count // 1000):
        s = random_settings(rng)
        if lib is None:
            s.reserve, s.legacy = 0, False
        out.append((f"random settings, {s.page_size}-byte pages", s, rng.getrandbits(64)))
    return out


# ---------------------------------------------------------------------
# What SQLite says about a database.

ENCODINGS = {"UTF-8": "utf-8", "UTF-16le": "utf-16-le", "UTF-16be": "utf-16-be"}


def render(v, enc):
    """A value from SQLite as `sqlite serve` writes a record value."""
    if v is None:
        return "null"
    if isinstance(v, int):
        return f"int:{v}"
    if isinstance(v, float):
        return f"real:{struct.unpack('>Q', struct.pack('>d', v))[0]}"
    if isinstance(v, str):
        return "text:" + hx(v.encode(enc, "surrogatepass"))
    return "blob:" + hx(v)


def ask_sqlite(path, meta):
    """What SQLite says about the database at `path`."""
    con = sqlite3.connect(path)
    con.text_factory = str
    try:
        def pragma(name):
            return con.execute(f"PRAGMA {name}").fetchone()[0]

        facts = {k: pragma(k) for k in ("page_size", "page_count", "freelist_count", "schema_version",
                                         "user_version", "application_id", "encoding", "auto_vacuum",
                                         "journal_mode", "default_cache_size")}
        facts["sqlite_version"] = con.execute("SELECT sqlite_version()").fetchone()[0]
        enc = ENCODINGS[facts["encoding"]]
        facts["dbstat"] = {r[2]: (r[0], r[1], r[3], r[4], r[5], r[6], r[7]) for r in con.execute(
            "SELECT name, path, pageno, pagetype, ncell, payload, unused, mx_payload FROM dbstat")}
        schema = con.execute("SELECT type, name, tbl_name, rootpage, sql FROM sqlite_schema").fetchall()
        facts["roots"] = {1: "sqlite_schema"}
        wr = {r[1]: r[4] for r in con.execute("PRAGMA table_list") if r[0] == "main"}
        trees = [table_tree(con, "sqlite_schema", 1, enc)]
        for typ, name, tbl, root, sql in schema:
            if not root:
                continue
            facts["roots"][root] = name
            if typ == "table" and not wr.get(name):
                trees.append(table_tree(con, name, root, enc))
            elif typ == "table":
                pk = [r[1] for r in con.execute(f"PRAGMA index_list({q(name)})") if r[3] == "pk"][0]
                trees.append(index_tree(con, name, pk, name, root, None, enc))
            else:
                trees.append(index_tree(con, name, name, tbl, root, meta["partial"].get(name), enc))
        facts["trees"] = trees
        facts["max_root"] = max([1] + [r[3] or 0 for r in schema])
        return facts
    finally:
        con.close()


def table_tree(con, name, root, enc):
    info = con.execute(f"PRAGMA table_info({q(name)})").fetchall()
    pks = [r for r in info if r[5]]
    alias = None
    if len(pks) == 1 and pks[0][2].upper() == "INTEGER":
        alias = pks[0][0]
    cols = [(r[1], affinity(r[2]), r[0] == alias) for r in info]
    rows = [(r[0], tuple(render(v, enc) for v in r[1:]))
            for r in con.execute(f"SELECT rowid, * FROM {q(name)} ORDER BY rowid")]
    return {"name": name, "root": root, "kind": "table", "cols": cols, "rows": rows}


def index_tree(con, name, index, table, root, cond, enc):
    info = {r[0]: r for r in con.execute(f"PRAGMA table_info({q(table)})")}
    xinfo = con.execute(f"PRAGMA index_xinfo({q(index)})").fetchall()
    cols, exprs = [], []
    for r in xinfo:
        if r[1] == -1:
            cols.append(("rowid", "INTEGER", False))
            exprs.append("rowid")
        else:
            cols.append((info[r[1]][1], affinity(info[r[1]][2]), False))
            exprs.append(q(info[r[1]][1]))
    sql = f"SELECT {', '.join(exprs)} FROM {q(table)}" + (f" WHERE {cond}" if cond else "")
    rows = [tuple(render(v, enc) for v in r) for r in con.execute(sql)]
    return {"name": name, "root": root, "kind": "index", "cols": cols, "rows": rows}


# ---------------------------------------------------------------------
# Reading the tool's output back.


def parse_cell(text):
    p, left, size, rowid, kept, overflow = text.split("/")

    def num(x):
        return None if x == "-" else int(x)

    return num(p), (num(left), num(size), num(rowid), hex_field(kept), num(overflow))


def parse_page(text):
    """A page as `showPage` writes it, back in the model's form."""
    head, _, cells = text.partition(" |")
    t, ffb, count, content, frag, right = head.split(" ")
    parsed = [parse_cell(c) for c in cells.split(" ") if c]
    return (int(t), int(ffb), int(count), int(content), int(frag), None if right == "-" else int(right),
            [p for p, _ in parsed], [c for _, c in parsed])


def parse_dump(lines):
    """The tool's dump: the header fields, the pages (None when FAIL),
    and the records of cells (None when FAIL)."""
    header, pages, records = None, {}, {}
    for line in lines:
        parts = line.split(" ")
        if parts[0] == "header":
            header = tuple(int(x) for x in parts[1:])
        elif parts[0] == "page":
            n = int(parts[1])
            pages[n] = None if parts[2:] == ["FAIL"] else parse_page(line.split(" ", 2)[2])
        elif parts[0] == "record":
            records[(int(parts[1]), int(parts[2]))] = None if parts[4:] == ["FAIL"] else parts[4:]
    return header, pages, records


# ---------------------------------------------------------------------
# The comparison with SQLite.

NAMED_ALIAS = "an INTEGER PRIMARY KEY column is NULL in the record; SQLite gives the rowid (2.3)"
NAMED_REAL = ("a whole-number float in a column of REAL affinity is kept as an integer; SQLite gives it "
              "back as a float (2.3)")
NAMED_SIGNED = "PRAGMA {} reads the 4-byte field as a signed integer"
NAMED_CACHE = "PRAGMA default_cache_size gives SQLite's built-in default, -2000, for a field of 0"
NAMED_UNUSED = ("dbstat counts unused bytes from the content start as stored, so 0 counts as 0, not "
                "65536 (1.6)")
NAMED_ENCODING_0 = ("SQLite writes a text encoding of 0 while a database has no schema, and reads it as "
                    "UTF-8; Spec/Defs.lean, after 1.3.13 (\"No other values are allowed\"), refuses the "
                    "header, so the tool reads nothing of the file")
NAMED_ROLE = "SQLite knows {} by where it is linked from; its bytes read as a b-tree page, for the model too"
ROLES = {"overflow": "an overflow page", "ptrmap": "a pointer-map page",
         "trunk": "a freelist trunk page", "leaf": "a freelist leaf page"}


class Check:
    """Counts of what was compared with SQLite, the named differences, and
    the failures."""

    def __init__(self):
        self.asked = collections.Counter()
        self.agree = collections.Counter()
        self.named = {}
        self.failures = []

    def ok(self, what):
        self.asked[what] += 1
        self.agree[what] += 1

    def name(self, what, reason, example):
        self.asked[what] += 1
        n, ex = self.named.get(reason, (0, None))
        self.named[reason] = (n + 1, ex or example)

    def fail(self, what, where, want, got):
        self.asked[what] += 1
        self.failures.append((where, want, got))


def float_bits_of_int(z):
    return f"real:{struct.unpack('>Q', struct.pack('>d', float(z)))[0]}"


def sqlite_reads(value, col, rowid):
    """What SQLite gives for a value of a record, read with its own rules
    for the column `col` (name, affinity, rowid alias); and the rule
    used, or None."""
    name, aff, alias = col
    if alias and value == "null":
        return f"int:{rowid}", NAMED_ALIAS
    if aff == "REAL" and value.startswith("int:"):
        return float_bits_of_int(int(value[4:])), NAMED_REAL
    return value, None


class Database:
    """One database made by SQLite: its file, what SQLite says about it,
    and the comparison of the tool's reading with it."""

    def __init__(self, index, label, settings, path, data, facts):
        self.index, self.label, self.settings, self.path = index, label, settings, path
        self.data, self.facts = data, facts
        self.spills = []          # (tree, entry index, payload)

    def where(self, more=""):
        return f"database {self.index} ({self.label})" + (f", {more}" if more else "")

    def compare_unread(self, check):
        """A database whose header the tool refuses: allowed only when the
        model refuses it for its text encoding of 0, and reads it, with
        SQLite's rule for that field, as SQLite does."""
        F = self.facts
        h, why = read_header(self.data)
        lenient, _ = read_header(self.data, encoding_zero=True)
        if (h is None and why == WHY_H_ENCODING and lenient is not None and lenient[H_ENCODING] == 0
                and F["encoding"] == "UTF-8" and lenient[H_PAGE_SIZE] == F["page_size"]
                and lenient[H_SIZE] == F["page_count"]):
            check.name("header fields", NAMED_ENCODING_0,
                       f"{self.where()}: PRAGMA encoding {F['encoding']}, the header "
                       f"{self.data[:100].hex()}")
        else:
            check.fail("header fields", self.where(), "a header the tool reads", "none")

    def compare_header(self, h, check):
        F = self.facts
        what = "header fields"
        if h is None:
            check.fail(what, self.where(), "a header", "none")
            return
        pairs = [("page_size", h[H_PAGE_SIZE], F["page_size"]),
                 ("page_count", h[H_SIZE], F["page_count"]),
                 ("freelist_count", h[H_FREE], F["freelist_count"]),
                 ("schema_version", h[H_COOKIE], F["schema_version"]),
                 ("encoding", {1: "UTF-8", 2: "UTF-16le", 3: "UTF-16be"}.get(h[H_ENCODING]), F["encoding"]),
                 ("journal_mode", (h[H_WRITE], h[H_READ]), (2, 2) if F["journal_mode"] == "wal" else (1, 1)),
                 ("auto_vacuum: largest root page", h[H_LARGEST],
                  F["max_root"] if F["auto_vacuum"] else 0),
                 ("auto_vacuum: incremental vacuum", h[H_INCREMENTAL], 1 if F["auto_vacuum"] == 2 else 0),
                 ("sqlite_version()", h[H_VERSION],
                  sum(int(x) * m for x, m in zip(F["sqlite_version"].split("."), (1000000, 1000, 1))))]
        for name, mine, theirs in pairs:
            if mine == theirs:
                check.ok(what)
            else:
                check.fail(what, self.where(f"PRAGMA {name}"), repr(theirs), repr(mine))
        for name, mine in (("user_version", h[H_USER]), ("application_id", h[H_APPID])):
            theirs = F[name]
            if mine == theirs:
                check.ok(what)
            elif theirs < 0 and mine == theirs + 2 ** 32:
                check.name(what, NAMED_SIGNED.format(name), f"{self.where()}: SQLite {theirs}, the tool {mine}")
            else:
                check.fail(what, self.where(f"PRAGMA {name}"), repr(theirs), repr(mine))
        theirs, mine = F["default_cache_size"], h[H_CACHE]
        if mine == theirs:
            check.ok(what)
        elif mine == 0 and theirs == -2000:
            check.name(what, NAMED_CACHE, f"{self.where()}: SQLite {theirs}, the tool {mine}")
        else:
            check.fail(what, self.where("PRAGMA default_cache_size"), repr(theirs), repr(mine))

    def walk(self, h, pages, records, check):
        """Walk every b-tree from its root by the tool's reading. The rows
        dbstat would give for each page, the role of each page, the
        entries of each tree, and the payloads that spill."""
        F, f = self.facts, self.data
        ps, U = h[H_PAGE_SIZE], h[H_PAGE_SIZE] - h[H_RESERVED]
        npages = len(f) // ps
        self.rows = {}            # page -> the dbstat row the tool's reading gives
        self.parent = {}          # page -> (ptrmap type, parent)
        self.entries = []         # per tree: [(rowid, ("dump", key) or ("spill", i))]
        self.keys = []            # per table: its interior keys, where they fall among the rowids
        bad = check.failures

        def page_bytes(n):
            return f[(n - 1) * ps:n * ps]

        for tree in F["trees"]:
            entries = []
            self.entries.append(entries)
            table = tree["kind"] == "table"
            types = (TABLE_INTERIOR, TABLE_LEAF) if table else (INDEX_INTERIOR, INDEX_LEAF)
            stack = [("page", tree["root"], "/", None)]
            order, keys = [], []
            while stack:
                item = stack.pop()
                if item[0] == "key":
                    keys.append((len(order), item[1], item[2]))
                    continue
                _, n, path, parent = item
                if n in self.rows or not 1 <= n <= npages:
                    bad.append((self.where(f"{tree['name']} page {n}, path {path}"),
                                "a page of the file reached once", "a page reached again or past the end"))
                    continue
                pg = pages.get(n)
                if pg is None:
                    self.rows[n] = (tree["name"], path, "FAIL")
                    continue
                t, ffb, count, content, frag, right, pointers, cells = pg
                if t not in types:
                    bad.append((self.where(f"page {n} of {tree['name']}"),
                                f"page type {' or '.join(map(str, types))}", f"page type {t}"))
                self.parent[n] = (1, 0) if parent is None else (5, parent)
                kept = sum(len(c[3]) for c in cells)
                biggest = max([c[1] or 0 for c in cells] + [0])
                hdr = (100 if n == 1 else 0) + (12 if t in INTERIOR else 8)
                free, at, seen = 0, ffb, set()
                pb = page_bytes(n)
                while at and at not in seen and at + 4 <= ps:
                    seen.add(at)
                    free += be(pb[at + 2:at + 4])
                    at = be(pb[at:at + 2])
                unused = content - hdr - 2 * count + frag + free
                self.rows[n] = (tree["name"], path, "internal" if t in INTERIOR else "leaf", count, kept,
                                unused, biggest)
                children = []
                for i, (p, c) in enumerate(zip(pointers, cells)):
                    left, size, rowid, local, overflow = c
                    if overflow is not None:
                        payload = self.follow(tree, n, path, i, c, U, ps, npages, check)
                        if payload is not None:
                            self.spills.append(payload)
                            ref = ("spill", len(self.spills) - 1)
                        else:
                            ref = ("broken", None)
                    else:
                        ref = ("dump", (n, p))
                    if t in INTERIOR:
                        children.append(("page", left, f"{path}{i:03x}/", n))
                        if table:
                            children.append(("key", rowid, f"page {n}, cell {i}"))
                    if table and t == TABLE_LEAF:
                        order.append((rowid, ref))
                    elif not table:
                        order.append((None, ref))
                if t in INTERIOR:
                    children.append(("page", right, f"{path}{count:03x}/", n))
                stack.extend(reversed(children))
            entries.extend(order)
            if table:
                self.keys.append((tree, keys, [r for r, _ in order]))

    def compare_keys(self, check):
        """The keys of table interior cells, as the tool reads them, among
        the rowids of the leaves: "pointers to the left of a X refer to
        b-tree pages on which all keys are less than or equal to X.
        Pointers to the right of X refer to pages where all keys are
        greater than X" (1.6)."""
        what = "table interior keys"
        for tree, keys, rowids in self.keys:
            last = None
            for pos, key, where in keys:
                before = rowids[pos - 1] if pos > 0 else None
                after = rowids[pos] if pos < len(rowids) else None
                if ((before is None or before <= key) and (after is None or key < after)
                        and (last is None or last < key)):
                    check.ok(what)
                else:
                    check.fail(what, self.where(f"table {tree['name']}, {where}"),
                               f"a key from {before} to below {after}, above {last}", f"key {key}")
                last = key

    def follow(self, tree, n, path, i, cell, U, ps, npages, check):
        """The whole payload of a cell that spills: the part the tool keeps
        on the page and the overflow pages, from the first one the tool
        reads (1.7). Adds the overflow pages' dbstat rows."""
        left, size, rowid, local, first = cell
        rest = size - len(local)
        count = -(-rest // (U - 4))
        out, at, prev = bytearray(local), first, n
        for j in range(count):
            if not 1 <= at <= npages or at in self.rows:
                check.failures.append((self.where(f"{tree['name']} page {n} cell {i}, overflow page {j}"),
                                       "a page of the file not used before", f"page {at}"))
                return None
            page = self.data[(at - 1) * ps:at * ps]
            part = min(U - 4, rest - len(out) + len(local))
            out += page[4:4 + part]
            last = j == count - 1
            self.rows[at] = (tree["name"], f"{path}{i:03x}+{j:06x}", "overflow", 0, part,
                             (U - 4 - part) if last else 0, 0)
            self.parent[at] = (3, n) if j == 0 else (4, prev)
            prev, at = at, be(page[:4])
        if at != 0:
            check.failures.append((self.where(f"{tree['name']} page {n} cell {i}"),
                                   "the overflow chain ends where the payload size says",
                                   f"page {prev} links on to page {at}"))
        return bytes(out)

    def compare_pages(self, h, pages, check):
        """dbstat, page by page; the pages SQLite does not read as b-tree
        pages; the freelist and pointer-map pages."""
        F, f = self.facts, self.data
        ps, U = h[H_PAGE_SIZE], h[H_PAGE_SIZE] - h[H_RESERVED]
        stat = F["dbstat"]
        npages = F["page_count"]
        what = "dbstat rows"
        for n in sorted(set(stat) | set(self.rows)):
            theirs, mine = stat.get(n), self.rows.get(n)
            if theirs == mine:
                check.ok(what)
            elif (theirs and mine and theirs[:5] == mine[:5] and theirs[6] == mine[6] and mine[2] != "overflow"
                  and pages.get(n) and pages[n][3] == 65536 and theirs[5] == mine[5] - 65536):
                check.name(what, NAMED_UNUSED, f"{self.where(f'page {n}')}: dbstat {theirs}, the tool's "
                                               f"reading {mine}")
            else:
                check.fail(what, self.where(f"page {n}"), f"dbstat {theirs}", f"from the tool {mine}")
        # The pages dbstat does not list.
        roles = {}
        if h[H_LARGEST]:
            J = U // 5
            p = 2
            while p <= npages:
                roles[p] = "ptrmap"
                p += J + 1
        trunk, seen = h[H_TRUNK], set()
        while trunk:
            if trunk in seen or not 1 <= trunk <= npages:
                check.fail("pages accounted for", self.where(f"freelist trunk page {trunk}"),
                           "a page of the file", "a page past the end or reached again")
                break
            seen.add(trunk)
            roles[trunk] = "trunk"
            page = f[(trunk - 1) * ps:trunk * ps]
            for k in range(min(be(page[4:8]), (U - 8) // 4)):
                roles[be(page[8 + 4 * k:12 + 4 * k])] = "leaf"
            trunk = be(page[:4])
        free = [p for p, r in roles.items() if r in ("trunk", "leaf")]
        for p in free:
            self.parent.setdefault(p, (2, 0))
        listed = set(stat)
        overlap = sorted(set(roles) & listed)
        missing = sorted(set(range(1, npages + 1)) - listed - set(roles))
        if overlap or missing or len(free) != h[H_FREE] or max(list(roles) + [0]) > npages:
            check.fail("pages accounted for", self.where(), "every page once: in dbstat, on the freelist "
                       "or a pointer-map page", f"in two of them {overlap[:5]}, in none {missing[:5]}, "
                       f"{len(free)} freelist pages for {h[H_FREE]}")
        else:
            check.ok("pages accounted for")
        what = "pages SQLite does not read as b-tree pages"
        for n in range(1, npages + 1):
            role = "overflow" if stat.get(n, ("", "", ""))[2] == "overflow" else roles.get(n)
            if role is None:
                continue
            got = pages.get(n)
            if got is None:
                check.ok(what)
            else:
                pg, _ = read_page(h, f, n)
                if pg is not None:
                    check.name(what, NAMED_ROLE.format(ROLES[role]), f"{self.where(f'page {n}')}: page {n} "
                               f"{show_page(got)[:120]}")
                else:
                    check.fail(what, self.where(f"page {n}"), "FAIL, as the model reads it",
                               show_page(got)[:120])
        # Pointer-map entries against the tree the tool reads.
        what = "pointer-map entries"
        if h[H_LARGEST]:
            J = U // 5
            for n in range(3, npages + 1):
                if roles.get(n) == "ptrmap":
                    continue
                base = 2 + ((n - 3) // (J + 1)) * (J + 1)
                at = (base - 1) * ps + 5 * (n - base - 1)
                theirs = (f[at], be(f[at + 1:at + 5]))
                mine = self.parent.get(n)
                if theirs == mine:
                    check.ok(what)
                else:
                    check.fail(what, self.where(f"page {n}"), f"pointer-map entry {theirs}",
                               f"from the tool {mine}")

    def compare_entries(self, records, spilled, check):
        """The rows and index entries the tool reads against SQLite's."""
        for tree, entries in zip(self.facts["trees"], self.entries):
            values = []
            for rowid, (src, key) in entries:
                if src == "dump":
                    values.append(records.get(key, "missing"))
                elif src == "spill":
                    a = spilled[key]
                    values.append(a[3:].split(" ") if a.startswith("OK ") else None)
                else:
                    values.append(None)
            if tree["kind"] == "table":
                self.compare_table(tree, entries, values, check)
            else:
                self.compare_index(tree, values, check)

    def compare_table(self, tree, entries, values, check):
        what = "table rows"
        rows = tree["rows"]
        if len(rows) != len(entries):
            check.fail(what, self.where(f"table {tree['name']}"), f"{len(rows)} rows",
                       f"{len(entries)} cells")
        for (rowid, _), vs, (srowid, svals) in zip(entries, values, rows):
            where = self.where(f"table {tree['name']}, rowid {srowid}")
            if rowid != srowid:
                check.fail(what, where, f"rowid {srowid}", f"rowid {rowid}")
                continue
            if vs is None or vs == "missing" or len(vs) != len(svals):
                check.fail(what, where, " ".join(svals)[:160], repr(vs)[:160])
                continue
            reasons, ok = [], True
            for v, sv, col in zip(vs, svals, tree["cols"]):
                if v == sv:
                    continue
                read, rule = sqlite_reads(v, col, rowid)
                if rule and read == sv:
                    reasons.append((rule, f"{where}, column {col[0]}: SQLite {sv}, the tool {v}"))
                else:
                    ok = False
            if not ok:
                check.fail(what, where, " ".join(svals)[:160], " ".join(vs)[:160])
            elif reasons:
                first = {}
                for r, ex in reasons:
                    first.setdefault(r, ex)
                check.name(what, "; ".join(sorted(first)), "; ".join(first[r] for r in sorted(first)))
            else:
                check.ok(what)

    def compare_index(self, tree, values, check):
        what = "index entries"
        theirs = collections.Counter(tree["rows"])
        mine = collections.Counter()
        why = {}
        for vs in values:
            if vs is None or vs == "missing" or len(vs) != len(tree["cols"]):
                check.fail(what, self.where(f"index {tree['name']}"), "an entry", repr(vs)[:160])
                continue
            read, rules = [], set()
            for v, col in zip(vs, tree["cols"]):
                r, rule = sqlite_reads(v, (col[0], col[1], False), None)
                read.append(r)
                if rule:
                    rules.add(rule)
            read = tuple(read)
            mine[read] += 1
            if rules:
                where = self.where(f"index {tree['name']}")
                why[read] = (rules, f"{where}: SQLite {' '.join(read)[:100]}, the tool {' '.join(vs)[:100]}")
        for entry, k in mine.items():
            matched = min(k, theirs.get(entry, 0))
            for _ in range(matched):
                if entry in why:
                    check.name(what, "; ".join(sorted(why[entry][0])), why[entry][1])
                else:
                    check.ok(what)
            for _ in range(k - matched):
                check.fail(what, self.where(f"index {tree['name']}"), "no such entry in SQLite",
                           " ".join(entry)[:160])
        for entry, k in theirs.items():
            for _ in range(k - min(k, mine.get(entry, 0))):
                check.fail(what, self.where(f"index {tree['name']}"), " ".join(entry)[:160],
                           "no such entry read by the tool")


# ---------------------------------------------------------------------
# Running a program over request lines.


def run_lines(cmd, lines, timeout=TIMEOUT, cwd=None, env=None):
    """Send `lines` to `cmd` and return its answer lines and a note on
    how the run failed, or None."""
    raw = "".join(lines).encode("utf-8")
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, cwd=cwd, env=env)
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf):
        while chunk := stream.read1(1 << 16):
            buf += chunk

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out)),
               threading.Thread(target=drain, args=(proc.stderr, err))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    return answers, problem


def run_parallel(cmd, lines, jobs):
    """`run_lines` over `jobs` processes, each given a run of the lines
    in order; the answers in order, and the problems."""
    size = -(-len(lines) // jobs) if lines else 0
    chunks = [lines[k:k + size] for k in range(0, len(lines), size)] if size else [[]]
    results = [None] * len(chunks)

    def one(k):
        results[k] = run_lines(cmd, chunks[k])

    threads = [threading.Thread(target=one, args=(k,)) for k in range(len(chunks))]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    answers, problems = [], []
    for chunk, (got, problem) in zip(chunks, results):
        if problem:
            problems.append(problem)
        if len(got) != len(chunk):
            problems.append(f"{len(got)} answers for {len(chunk)} requests")
            got = (got + [""] * len(chunk))[:len(chunk)]
        answers += got
    return answers, problems


def run_dump(path):
    """`sqlite dump path`: its lines, exit status, and a problem or None."""
    try:
        p = subprocess.run([str(EXE), "dump", str(path)], capture_output=True, timeout=TIMEOUT)
    except (OSError, subprocess.SubprocessError) as e:
        return [], None, str(e)
    text = p.stdout.decode("utf-8", "backslashreplace")
    lines = text.split("\n")
    problem = None
    if text and not text.endswith("\n"):
        problem = "the last line has no LF"
    if lines and lines[-1] == "":
        lines.pop()
    return lines, p.returncode, problem


# ---------------------------------------------------------------------
# Malformed and odd requests, and the command line.

MALFORMED = [
    "", " ", "\t", "varint", "varint 00 00", "varint 0", "varint 0A", "varint 0x00", "varint zz",
    "varint ", "varint  00", " varint 00", "VARINT 00", "Varint 00", "varint\t00", "varint --",
    "varint +00", "varint é0", "header", "header 53 51", "header -0", "page 1", "page 1 00 00",
    "page -1 00", "page +1 00", "page 1.0 00", "page x 00", "page  00", "page 1e3 00", "page ٣ 00",
    "page 1_0 00", "page ０ 00", "page 1 0G", "record", "record 0", "record 00 00", "record 02 0105",
    "local 13 4096", "local 13 4096 100 1", "local 3 4096 100", "local 0 4096 100", "local 14 4096 100",
    "local 256 4096 100", "local 269 4096 100", "local 013x 4096 100", "local 13 -1 100",
    "local 13 4096 -", "local - 4096 100", "local 13 4096 1e3", "local 13 4096 ９", "local 13  4096 1",
    "local 13 4096 1 ", "dump x", "serve", "pages 1 00", "records 00", "varint00", "local13 1 1",
    "varint FF", "header 53514C69", "record 0A01", "page 1 0D00", "varint Ff", "varint fF",
]
ODD = ["varint -", "header -", "record -", "page 0 -", "page 1 -", "local 013 04096 010000",
       "local 2 0 0", "local 5 0 0", "local 10 4 5", "local 13 99999999999999999999999 5",
       "page 99999999999999999999999 " + SPEC_HEADER.hex(), "page 0001 " + ONE_PAGE_FILE.hex(),
       "varint " + "ff" * 20, "record " + "ff" * 9]
# Last lines with no LF, with CR LF, with a lone CR: (request, answer).
AT_EOF = [("varint 00", "OK 0 1 -"), ("record 020105\r\n", "OK int:5"), ("local 13 4096 10000", "OK 1816"),
          ("varint 00\r", "error")]


def cli_cases(folder, sample):
    """Runs of the command line: (arguments, standard input, the lines
    the run must print on standard output, its exit status), from the
    model and the header of Main.lean."""
    folder = Path(folder)
    cases = []
    lines, status = model_dump(sample)
    db = folder / "cli.db"
    db.write_bytes(sample)
    cases.append((["dump", str(db)], b"", lines, status))
    for name, data in (("noheader.db", b"not a database file at all\n" * 40), ("empty.db", b""),
                       ("headeronly.db", sample[:100]), ("partial.db", sample + b"\x0d" * 300),
                       ("cut.db", sample[:99])):
        path = folder / name
        path.write_bytes(data)
        lines, status = model_dump(data)
        cases.append((["dump", str(path)], b"", lines, status))
    cases.append((["dump", str(folder / "does-not-exist.db")], b"", [], 2))
    sub = folder / "a-folder"
    sub.mkdir(exist_ok=True)
    cases.append((["dump", str(sub)], b"", [], 2))
    cases.append((["serve"], b"", [], 0))
    for args in ([], ["dump"], ["dump", str(db), str(db)], ["serve", "x"], ["Dump", str(db)], ["bogus"],
                 ["header", "00"], ["--help"], ["dump", ""]):
        cases.append((args, b"", [], 2))
    return cases


def run_cli(cases):
    right, failures = 0, []
    for args, stdin, want, status in cases:
        try:
            p = subprocess.run([str(EXE)] + args, input=stdin, capture_output=True, timeout=600)
            text = p.stdout.decode("utf-8", "backslashreplace")
            got, code_ = (text[:-1].split("\n") if text.endswith("\n") else
                          ([text] if text else [])), p.returncode
        except (OSError, subprocess.SubprocessError) as e:
            got, code_ = [str(e)], None
        if (got, code_) == (want, status):
            right += 1
        else:
            first = next((i for i, (a, b) in enumerate(zip(want, got)) if a != b), min(len(want), len(got)))
            failures.append((f"sqlite {' '.join(args)}"[:120],
                             f"{len(want)} lines, exit {status}; line {first + 1}: "
                             f"{(want[first] if first < len(want) else '(none)')[:120]}",
                             f"{len(got)} lines, exit {code_}; line {first + 1}: "
                             f"{(got[first] if first < len(got) else '(none)')[:120]}"))
    return right, failures


# ---------------------------------------------------------------------


def lean_version():
    try:
        out = subprocess.run(["lean", "--version"], cwd=ROOT, capture_output=True, text=True,
                             errors="backslashreplace", timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def first_line(cmd):
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        return (out.stdout or out.stderr).strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError, IndexError):
        return "unknown"


def count_arg(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def code(text):
    """`text` as Markdown inline code, whatever backticks it holds."""
    return f"`` {text} ``" if "`" in text else f"`{text}`"


def short(text, n=200):
    return text if len(text) <= n else text[:n] + f"... ({len(text)} characters)"


def tally(counter):
    return ", ".join(f"{k} {v}" for k, v in sorted(counter.items(), key=lambda kv: (-kv[1], kv[0])))


# ---------------------------------------------------------------------
# All the requests sent to `sqlite serve`, after the databases are made.


def every_byte_value(label, data):
    for i in range(len(data)):
        for v in range(256):
            if v != data[i]:
                yield (label, "header", [data[:i] + bytes([v]) + data[i + 1:]])


def inputs(seed, count, dbs):
    rng = random.Random(seed)
    for op, args, _ in SPEC_CASES:
        yield ("Spec.lean's examples and rejects", op, args)
    yield from varint_sets(rng)
    for _ in range(count):
        yield ("random bytes", "varint", [random_varint(rng)])
    # Headers.
    for db in dbs:
        yield ("the header of a database made by SQLite", "header",
               [db.data[:100 + rng.choice((0, 0, 1, 28))]])
    for db in dbs[:2]:
        yield from every_byte_value("every value of every byte of a real header", db.data[:100])
    for v in range(65536):
        yield ("every value of the page size field", "header",
               [SPEC_HEADER[:16] + v.to_bytes(2, "big") + SPEC_HEADER[18:]])
    for ps in PAGE_SIZES:
        h = SPEC_HEADER[:16] + (1 if ps == 65536 else ps).to_bytes(2, "big") + SPEC_HEADER[18:]
        for i in range(18, 24):
            for v in range(256):
                yield ("every value of bytes 18 to 23, for each page size", "header",
                       [h[:i] + bytes([v]) + h[i + 1:]])
    for k in range(100):
        yield ("a real header cut short", "header", [dbs[0].data[:k]])
    for _ in range(count // 5):
        yield ("a header from random fields", "header", [random_header(rng)])
    # Records.
    for _ in range(count):
        cols, rec = random_record(rng)
        yield ("random record", "record", [rec])
        if rng.random() < 0.6:
            label, b = changed_record(rng, cols, rec)
            yield ("random record, " + label, "record", [b])
    for _ in range(count // 10):
        yield ("random bytes", "record", [rng.randbytes(rng.choice((1, 2, 3, 8, 30)))])
    # `local`.
    yield from local_sets(rng)
    for _ in range(count // 2):
        yield ("random", "local", random_local(rng))
    # Pages of the databases.
    for db in dbs:
        ps = db.settings.page_size
        npages = len(db.data) // ps
        if ps <= 2048:
            for n in range(0, min(npages, 8) + 1):
                yield ("each of the first pages of a database made by SQLite, the file cut after it",
                       "page", [n, db.data[:max(1, n) * ps]])
        if len(db.data) <= 131072:
            yield ("the last page of a database made by SQLite, and the page after it", "page",
                   [npages, db.data])
            yield ("the last page of a database made by SQLite, and the page after it", "page",
                   [npages + 1, db.data])
    for db in dbs:
        ps = db.settings.page_size
        npages = len(db.data) // ps
        picks = list(range(2, npages + 1))
        rng.shuffle(picks)
        for x in picks[:3 if ps >= 16384 else 40]:
            f = db.data[:ps] + db.data[(x - 1) * ps:x * ps]
            yield ("a page of a database made by SQLite, as page 2", "page", [2, f])
            if rng.random() < 0.25:
                yield ("a page of a database made by SQLite, as page 2, the file one byte short",
                       "page", [2, f[:-1]])
    readable = [db for db in dbs if read_header(db.data)[0] is not None]
    for label, op, (n, f) in edge_pages(rng):
        yield (label, op, [n, f])
        yield (label + ", the file one byte short", op, [n, f[:-1]])
    small = [db for db in readable if db.settings.page_size <= 4096]
    large = [db for db in readable if db.settings.page_size > 4096]
    for _ in range(count // 3):
        db = (rng.choice(large) if large and rng.random() < 0.01 else
              rng.choices(small, [1 / d.settings.page_size for d in small])[0])
        ps = db.settings.page_size
        npages = len(db.data) // ps
        x = rng.randint(1, npages)
        if x == 1 or rng.random() < 0.2:
            f, n = db.data[:ps], 1
        else:
            f, n = db.data[:ps] + db.data[(x - 1) * ps:x * ps], 2
        h, _ = read_header(f)
        label, b = changed_page(rng, h, f, n)
        yield ("a page of a database made by SQLite, " + label, "page", [n, b])
    for _ in range(count // 5):
        r = rng.random()
        ps = 512 if r < 0.55 else 1024 if r < 0.75 else rng.choice((2048, 4096)) if r < 0.995 else \
            rng.choice((8192, 16384, 32768, 65536))
        reserved = random_reserved(rng, ps)
        if ps == 65536 and rng.random() < 0.5:
            reserved = 0
        f, defect = built_page(rng, ps, reserved, rng.choice((1, 2)))
        yield ("a built page, " + defect, "page", [2 if len(f) > ps else 1, f])


def changed_databases(rng, dbs, folder, k):
    """k copies of small databases with bytes changed in a few pages, to
    dump."""
    readable = [db for db in dbs if read_header(db.data)[0] is not None]
    small = [db for db in readable if len(db.data) <= 262144] or readable
    out = []
    for i in range(k):
        db = rng.choice(small)
        h, _ = read_header(db.data)
        f = db.data
        ps = h[H_PAGE_SIZE]
        for _ in range(rng.randint(1, 3)):
            n = rng.randint(1, len(f) // ps)
            label, g = changed_page(rng, h, f, n)
            if len(g) == len(f) and g[:100] == f[:100]:
                f = g
        path = Path(folder) / f"changed{i}.db"
        path.write_bytes(f)
        out.append((path, f))
    return out


# ---------------------------------------------------------------------


def main():
    global EXE
    sys.set_int_max_str_digits(0)
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261028)
    ap.add_argument("--count", type=count_arg, default=100000)
    ap.add_argument("--no-oracles", action="store_true",
                    help="compare with the model only, as tests/plant_bugs.py does")
    ap.add_argument("--no-build", action="store_true",
                    help="use .lake/build/bin/sqlite as it is, without `lake build sqlite`")
    args = ap.parse_args()
    os.environ["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{os.environ.get('PATH', '')}"
    started = time.monotonic()

    def give_up(why):
        write(["# Test results", "", "- Oracle: none ran", f"- Seed: {args.seed}", "- Inputs: 0",
               f"- Failures: 1 ({why})", ""])
        sys.exit(why)

    if args.no_build:
        built = "`.lake/build/bin/sqlite` as it was, not rebuilt (`--no-build`)"
        newest = max(p.stat().st_mtime for p in (ROOT / "Main.lean", ROOT / "Sqlite" / "Basic.lean",
                                                   ROOT / "Spec" / "Defs.lean"))
        if not BUILT_EXE.exists():
            give_up("`--no-build`, and there is no .lake/build/bin/sqlite")
        if BUILT_EXE.stat().st_mtime < newest:
            built += "; it is older than the sources"
    else:
        built = "built by `lake build sqlite`"
        try:
            build = subprocess.run(["lake", "build", "sqlite"], cwd=ROOT, capture_output=True,
                                   text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
            if build.returncode != 0:
                print(build.stdout + build.stderr)
                give_up("`lake build sqlite` failed")
        except (OSError, subprocess.SubprocessError) as e:
            give_up(f"`lake build sqlite` failed: {e}")

    failures = []
    with tempfile.TemporaryDirectory() as tmpname:
        tmp = Path(tmpname)
        EXE = tmp / "sqlite"
        shutil.copy2(BUILT_EXE, EXE)
        exe_hash = hashlib.sha256(EXE.read_bytes()).hexdigest()
        try:
            lib, lib_why = Lib(tmp), None
        except Exception as e:  # without ctypes, no reserved bytes and no legacy format
            lib, lib_why = None, str(e).splitlines()[0][:200] if str(e) else type(e).__name__
        left_out = []
        oracle = not args.no_oracles
        if args.no_oracles:
            left_out.append(("SQLite", "--no-oracles"))
        elif sqlite3.sqlite_version != SQLITE_PINNED:
            left_out.append(("SQLite", f"{sqlite3.sqlite_version} is installed, not {SQLITE_PINNED}"))
            oracle = False
        else:
            try:
                sqlite3.connect(":memory:").execute("SELECT * FROM dbstat").fetchall()
            except sqlite3.Error as e:
                left_out.append(("SQLite", f"no dbstat: {e}"))
                oracle = False
        for name, why in left_out:
            print(f"oracle left out: {name}: {why}")

        # The databases.
        dbs = []
        for i, (label, s, sd) in enumerate(all_databases(args.seed, args.count, lib)):
            path = tmp / f"db{i}.db"
            meta = make_database(path, s, random.Random(sd), lib)
            data = path.read_bytes()
            facts = None
            if oracle:
                facts = ask_sqlite(path, meta)
                if path.read_bytes() != data:
                    failures.append((f"database {i}", "the same file after SQLite is asked about it",
                                     "a changed file"))
            dbs.append(Database(i, label, s, path, data, facts))
        made = time.monotonic()
        print(f"{len(dbs)} databases made in {made - started:.0f} s", flush=True)
        changed = changed_databases(random.Random(args.seed + 5), dbs, tmp, 4 + args.count // 2000)

        # The requests.
        items = list(inputs(args.seed, args.count, dbs))
        lines = [request(op, a) + ("\r\n" if i % 7 == 6 else "\n") for i, (_, op, a) in enumerate(items)]
        odd = MALFORMED + ODD
        served = {}

        def serve():
            served["out"] = run_parallel([str(EXE), "serve"], lines + [m + "\n" for m in odd], JOBS)

        server = threading.Thread(target=serve)
        server.start()
        wants = [model(op, a) for _, op, a in items]
        server.join()
        out, problems = served["out"]
        print(f"{len(items)} requests answered, {time.monotonic() - made:.0f} s", flush=True)
        for problem in problems:
            failures.append(("(whole run)", "a clean run", problem))
        tool, odd_out = out[:len(items)], out[len(items):]
        by_label = collections.Counter(f"{label} ({op})" for label, op, _ in items)
        by_op = collections.Counter(op for _, op, _ in items)
        refused = collections.Counter()
        differ_model = 0
        spec_right = 0
        for i, ((label, op, a), (want, why), got) in enumerate(zip(items, wants, tool)):
            if why is not None:
                refused[(op, why)] += 1
            if label == "Spec.lean's examples and rejects":
                spec_right += want == SPEC_CASES[i][2]
                if want != SPEC_CASES[i][2]:
                    failures.append((f"the model on {short(request(op, a), 120)}", SPEC_CASES[i][2], want))
            if got != want:
                differ_model += 1
                failures.append((short(lines[i].rstrip("\r\n"), 160), short(want, 160), short(got, 160)))
        del lines, wants, tool
        malformed_right = sum(1 for a in odd_out[:len(MALFORMED)] if a == "error")
        for m in MALFORMED:
            if model_line(m + "\n") != "error":
                failures.append((f"the model on {m!r}", "error", model_line(m + "\n")))
        odd_right = 0
        for m, a in zip(odd, odd_out):
            want = model_line(m + "\n")
            if a == want:
                odd_right += m in ODD
            else:
                failures.append((f"request {short(m, 100)!r}", short(want, 100), short(a, 100)))
        eof_right = 0
        for req, want in AT_EOF:
            if model_line(req) != want:
                failures.append((f"the model on {req!r} at end of input", want, model_line(req)))
            got, problem = run_lines([str(EXE), "serve"], [req], timeout=60)
            if got == [want] and not problem:
                eof_right += 1
            else:
                failures.append((repr(req) + " (at end of input)", want, f"{got} {problem or ''}".strip()))

        # The dumps.
        check = Check()
        dump_kinds = collections.Counter()
        page_kinds = collections.Counter()
        dumps_right = 0
        dump_lines = 0
        jobs = [(db.path, db.data, db) for db in dbs] + [(p, f, None) for p, f in changed]
        with concurrent.futures.ThreadPoolExecutor(JOBS) as pool:
            results = pool.map(lambda job: run_dump(job[0]), jobs)
            for (path, data, db), (got, status, problem) in zip(jobs, results):
                label = "a database made by SQLite" if db else "a database made by SQLite, bytes changed"
                by_label[f"{label} (dump)"] += 1
                by_op["dump"] += 1
                want, want_status = model_dump(data)
                dump_lines += len(want)
                for line in want:
                    if line.startswith("page "):
                        page_kinds["FAIL" if line.endswith(" FAIL") else line.split(" ")[2]] += 1
                    elif line.startswith("record ") and line.endswith(" FAIL"):
                        page_kinds["record FAIL"] += 1
                if (got, status, problem) == (want, want_status, None):
                    dumps_right += 1
                else:
                    differ_model += 1
                    first = next((k for k, (a, b) in enumerate(zip(want, got)) if a != b),
                                 min(len(want), len(got)))
                    failures.append((f"sqlite dump {path.name} ({db.where() if db else 'bytes changed'})",
                                     f"{len(want)} lines, exit {want_status}; line {first + 1}: "
                                     + short(want[first] if first < len(want) else "(none)", 160),
                                     f"{len(got)} lines, exit {status}{', ' + problem if problem else ''}; "
                                     f"line {first + 1}: " + short(got[first] if first < len(got) else "(none)",
                                                                   160)))
                if db is not None and oracle:
                    h, pages, records = parse_dump(got)
                    try:
                        if h is None:
                            db.compare_unread(check)
                        else:
                            db.compare_header(h, check)
                            db.walk(h, pages, records, check)
                            db.compare_keys(check)
                            db.compare_pages(h, pages, check)
                            db.parsed = (h, pages, records)
                    except Exception as e:  # the tool's dump did not read back
                        check.fail("databases read back", db.where(), "a dump that reads back",
                                   f"{type(e).__name__}: {e}")
        print(f"{len(jobs)} dumps, {time.monotonic() - made:.0f} s", flush=True)

        # Payloads that spill, joined from their overflow pages.
        spill_items = [(db, k, p) for db in dbs for k, p in enumerate(db.spills)]
        spill_lines = [request("record", [p]) + "\n" for _, _, p in spill_items]
        spill_out, problems = run_parallel([str(EXE), "serve"], spill_lines, JOBS)
        for problem in problems:
            failures.append(("(payloads that spill)", "a clean run", problem))
        spilled = {}
        for (db, k, p), got in zip(spill_items, spill_out):
            want, why = model("record", [p])
            by_label["a payload that spills, joined from its overflow pages (record)"] += 1
            by_op["record"] += 1
            if why is not None:
                refused[("record", why)] += 1
            if got != want:
                differ_model += 1
                failures.append((short(request("record", [p]), 160), short(want, 160), short(got, 160)))
            spilled.setdefault(db.index, {})[k] = got
        if oracle:
            for db in dbs:
                if hasattr(db, "parsed"):
                    try:
                        db.compare_entries(db.parsed[2], spilled.get(db.index, {}), check)
                    except Exception as e:
                        check.fail("databases read back", db.where(), "rows that read back",
                                   f"{type(e).__name__}: {e}")
        failures += check.failures

        # The command line.
        sample = min((db.data for db in dbs if read_header(db.data)[0] is not None
                      and 2 * db.settings.page_size <= len(db.data)), key=len)
        cli = cli_cases(tmp, sample)
        cli_right, cli_failures = run_cli(cli)
        failures += cli_failures

    n_inputs = sum(by_label.values())
    settings = [db.settings for db in dbs]
    pages_total = sum(len(db.data) // db.settings.page_size for db in dbs)
    lines_out = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Lean: {lean_version()}",
        f"- Executable: {built}; SHA-256 of the copy run {exe_hash}",
        "- Oracle: the model of the file format in `tests/run_tests.py`"
        + ("" if not oracle else f"; SQLite {sqlite3.sqlite_version}"),
    ]
    if oracle:
        con = sqlite3.connect(":memory:")
        source = con.execute("SELECT sqlite_source_id()").fetchone()[0]
        con.close()
        package = first_line(["dpkg-query", "-W", "-f", "${Package} ${Version}\n", "libsqlite3-0"])
        lines_out.append(
            f"- SQLite: {sqlite3.sqlite_version} ({source})"
            + (f", the library of Debian package {package}" if package != "unknown" else "")
            + f", through the sqlite3 module of Python {sys.version.split()[0]}, with dbstat")
    lines_out += [
        "- Oracles left out: " + ("; ".join(f"{n} ({why})" for n, why in left_out) or "none"),
        f"- Seed: {args.seed}",
        f"- Inputs: {n_inputs}",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        "- Requests: " + ", ".join(f"`{op}` {n}" for op, n in sorted(by_op.items())),
        f"- Answers that differ from the model: {differ_model}",
        f"- Spec.lean's `examples` and `rejects`, answered by the model as Spec.lean states them: "
        f"{spec_right} of {len(SPEC_CASES)}",
    ]
    for op, name in (("varint", "Varints"), ("header", "Headers"), ("page", "Pages asked with `page`"),
                     ("record", "Records")):
        n = by_op[op]
        no = sum(v for (o, _), v in refused.items() if o == op)
        reasons = collections.Counter({why: v for (o, why), v in refused.items() if o == op})
        lines_out.append(f"- {name}: {n}, of which the model reads {n - no}; why it refuses the others: "
                         + (tally(reasons) or "none"))
    lines_out += [
        f"- Databases made by SQLite: {len(dbs)} ({len(FIXED_DATABASES)} fixed, the rest random), "
        f"{pages_total} pages in all. Page sizes: "
        + tally(collections.Counter(s.page_size for s in settings))
        + "; with reserved bytes: " + str(sum(1 for s in settings if s.reserve))
        + "; text encodings: " + tally(collections.Counter(s.encoding or "UTF-8" for s in settings))
        + "; auto_vacuum: " + tally(collections.Counter(("none", "full", "incremental")[s.auto_vacuum or 0]
                                                      for s in settings))
        + f"; WAL: {sum(1 for s in settings if s.wal)}; legacy file format: "
        f"{sum(1 for s in settings if s.legacy)}; secure_delete off: "
        f"{sum(1 for s in settings if s.secure_delete == 'OFF')}"
        + ("" if lib else f"; reserved bytes and the legacy format not set ({lib_why})"),
        f"- Dumps: {len(jobs)} ({len(changed)} with bytes changed), {dump_lines} lines, as the model "
        f"prints them: {dumps_right} of {len(jobs)}. Pages in them, by type: "
        + tally(collections.Counter({("page type " + k if k != "FAIL" else "not read (FAIL)")
                                     if k != "record FAIL" else "records not read (FAIL)": v
                                     for k, v in page_kinds.items()})),
    ]
    if oracle:
        lines_out.append(
            "- Agreement with SQLite (the rest are the named differences below, or failures): "
            + ", ".join(f"{what} {check.agree[what]} of {check.asked[what]}" for what in sorted(check.asked)))
        lines_out.append(f"- Payloads that spill, joined from the part the tool keeps on the page and the "
                         f"overflow pages, and read whole by `record`: {len(spill_items)}")
    else:
        lines_out.append("- Agreement with SQLite: SQLite left out")
    lines_out += [
        f"- Malformed requests answered `error`: {malformed_right} of {len(MALFORMED)}; odd but "
        f"well-formed requests answered as the model says: {odd_right} of {len(ODD)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: "
        f"{eof_right} of {len(AT_EOF)}",
        f"- Command line (`sqlite dump`, `sqlite serve` and wrong arguments), printing and exiting as "
        f"the model says: {cli_right} of {len(cli)}",
        f"- Time: {time.monotonic() - started:.0f} s",
        f"- Failures: {len(failures)}",
        "",
    ]
    if oracle:
        lines_out += ["## Where SQLite and the tool differ", "",
                      "Each disagreement is counted under the reason the model confirms: the model's "
                      "reading, with SQLite's own rule, gives SQLite's answer. The first input that "
                      "showed it is given.", ""]
        if not check.named:
            lines_out.append("No disagreement.")
        for reason, (n, example) in sorted(check.named.items(), key=lambda kv: -kv[1][0]):
            lines_out.append(f"- {reason}: {n}; for example {short(example, 300)}")
        lines_out.append("")
    if failures:
        lines_out += ["## Failures", ""]
        lines_out += [f"- {code(short(req, 300))}: expected {code(want)}, got {code(got)}"
                      for req, want, got in failures[:60]]
        if len(failures) > 60:
            lines_out.append(f"- and {len(failures) - 60} more")
        lines_out.append("")
    write(lines_out)
    print(f"{n_inputs} inputs, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
