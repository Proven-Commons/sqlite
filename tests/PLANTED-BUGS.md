# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `Sqlite/Basic.lean` (39 bugs) or to `Main.lean` (7), tested with `tests/run_tests.py --count 3000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the ninth byte of a varint gives only its low seven bits | 954 |
| a byte 0x80 ends a varint, as if its continuation bit were clear | 2412 |
| a varint byte that goes on gives its continuation bit too | 21138 |
| the page size 1 is not read as 65536 | 12906 |
| a read version of 0 is accepted | 3 |
| a usable size of 479 is accepted | 1 |
| only the maximum embedded payload fraction is checked | 1051 |
| the last of the 20 bytes reserved for expansion is not checked | 512 |
| schema format 5 is accepted | 9 |
| text encoding 0 is accepted | 13 |
| the index leaf page type is 11, not 10 | 19549 |
| page type 2 is read as a table interior page | 247 |
| the right-most pointer is read as 2 bytes | 487 |
| on a leaf page, a content start of 0 is not read as 65536 | 8 |
| a cell may start one byte before the cell content area | 136 |
| a cell may end one byte past the usable size | 36 |
| the bound on the cell pointer array counts one byte a pointer | 86 |
| the cell content area may start in the reserved region | 56 |
| the page header of an interior page is taken as 8 bytes in the bound on the pointer array | 51 |
| the page may be one byte short of the page size | 0 |
| X is U-35 on index leaf pages, not on table leaf pages | 18470 |
| X on index pages is one more | 2067 |
| M divides by 256, not 255 | 16763 |
| K takes the remainder by U-5, not U-4 | 25765 |
| a K equal to X is not kept on the page | 2060 |
| the overflow page number is read as 3 bytes | 469 |
| a cell that spills is not counted with its overflow page number | 7 |
| rowids of 2^63 and more are not read as negative | 142 |
| the rowid of a table interior cell is not read as a 64-bit two's complement integer | 67 |
| serial type 5 takes 5 bytes, not 6 | 1140 |
| serial type 7 is not 8 bytes | 1357 |
| serial type 11 is read | 14 |
| an integer whose top bit is set and the rest clear is read as positive | 279 |
| serial type 7 is read as an integer | 1351 |
| serial type 9 is read as 0 | 657 |
| odd serial types are blobs and even ones text | 2273 |
| the header size is counted after a size varint of one byte, whatever its length | 248 |
| bytes after the last column are allowed | 223 |
| a record with no column is read | 70 |
| Main.lean: the CR of a CR LF line ending is kept | 38834 |
| Main.lean: upper-case hex digits are read | 1 |
| Main.lean: a cell is printed with its rowid before its payload size | 1169 |
| Main.lean: the content start 65536 is printed as 0 | 12 |
| Main.lean: `sqlite dump` exits with 0 when the header is refused | 4 |
| Main.lean: `sqlite dump` leaves out the last page | 29 |
| Main.lean: `sqlite dump` prints the record of a cell that spills, from the part on the page | 26 |

Bugs caught: 45 of 46
