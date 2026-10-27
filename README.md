# sqlite

A Lean reader for the SQLite file format. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification. It is not SQLite itself. It reads SQLite files. It is not a database engine.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## Wave 1

This is one of the three Wave 1 projects in the founding brief, months 4 to 9, one squad each. The other two are the Cedar style policy engine and the Redis protocol parser. Redis already has a repo.

## First slice

- The 100 byte header.
- The page header.
- Records.

## Claims to prove

- The parser returns an error instead of reading outside the file.
- A record it reads stays inside its page.

## What is not in this slice

- Writing SQLite files.
- Querying. This is a file reader only.
- Any claim about a full database engine.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
