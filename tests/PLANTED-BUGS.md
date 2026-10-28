# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `Sqlite/Basic.lean` (40 bugs) or to `Main.lean` (7), tested with `tests/run_tests.py --count 3000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed. So does a run on other inputs than the unchanged code's: every run must give the same `- Inputs SHA-256:` line, which here is 51f296ed8bcf700cf86ce58a62ccd0eeb8291a87cd09c640cb5dd057fda50271.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the ninth byte of a varint gives only its low seven bits | 858 |
| a byte 0x80 ends a varint, as if its continuation bit were clear | 2187 |
| a varint byte that goes on gives its continuation bit too | 20785 |
| the page size 1 is not read as 65536 | 13370 |
| a read version of 0 is accepted | 13 |
| a usable size of 479 is accepted | 3 |
| only the maximum embedded payload fraction is checked | 5631 |
| the last of the 20 bytes reserved for expansion is not checked | 766 |
| schema format 5 is accepted | 15 |
| text encoding 0 is accepted, whatever the schema format | 48 |
| text encoding 0 is refused, even with schema format 0 | 12839 |
| the index leaf page type is 11, not 10 | 19520 |
| page type 2 is read as a table interior page | 240 |
| the right-most pointer is read as 2 bytes | 458 |
| on a leaf page, a content start of 0 is not read as 65536 | 3 |
| a cell may start one byte before the cell content area | 127 |
| a cell may end one byte past the usable size | 33 |
| the bound on the cell pointer array counts one byte a pointer | 73 |
| the cell content area may start in the reserved region | 46 |
| the page header of an interior page is taken as 8 bytes in the bound on the pointer array | 40 |
| the page may be one byte short of the page size | 193 |
| X is U-35 on index leaf pages, not on table leaf pages | 18358 |
| X on index pages is one more | 2052 |
| M divides by 256, not 255 | 16784 |
| K takes the remainder by U-5, not U-4 | 25782 |
| a K equal to X is not kept on the page | 2064 |
| the overflow page number is read as 3 bytes | 424 |
| a cell that spills is not counted with its overflow page number | 17 |
| rowids of 2^63 and more are not read as negative | 122 |
| the rowid of a table interior cell is not read as a 64-bit two's complement integer | 59 |
| serial type 5 takes 5 bytes, not 6 | 903 |
| serial type 7 is not 8 bytes | 1188 |
| serial type 11 is read | 9 |
| an integer whose top bit is set and the rest clear is read as positive | 170 |
| serial type 7 is read as an integer | 1180 |
| serial type 9 is read as 0 | 476 |
| odd serial types are blobs and even ones text | 2220 |
| the header size is counted after a size varint of one byte, whatever its length | 232 |
| bytes after the last column are allowed | 225 |
| a record with no column is read | 71 |
| Main.lean: the CR of a CR LF line ending is kept | 44306 |
| Main.lean: upper-case hex digits are read | 7 |
| Main.lean: a cell is printed with its rowid before its payload size | 965 |
| Main.lean: the content start 65536 is printed as 0 | 5 |
| Main.lean: `sqlite dump` exits with 0 when the header is refused | 3 |
| Main.lean: `sqlite dump` leaves out the last page | 30 |
| Main.lean: `sqlite dump` prints the record of a cell that spills, from the part on the page | 26 |

Bugs caught: 47 of 47
