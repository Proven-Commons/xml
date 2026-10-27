# xml

A Lean parser for a safe subset of XML. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification. It is not a full XML parser. It parses only the subset below.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

Elements, attributes, text, comments, processing instructions, character references, and CDATA sections. One root element. Attribute values are quoted. No document type declaration, no entity declarations, and no namespaces in this slice. A document containing a document type declaration is rejected, not parsed leniently.

## Main claim

Printing a parsed document gives a document that parses to the same tree. A document with a document type declaration, an undefined entity reference, or mismatched tags is rejected. The parser never expands an entity, because no entities exist in the subset.

## Test oracles

- Python ElementTree, Go encoding/xml, and Rust quick-xml, each in a strict subset mode. These parsers disagree outside the subset, on document type and entity handling. The differential harness counts out of subset cases separately, not as failures.

## Score

14 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- Document type declarations.
- Entities.
- Namespaces.
- Full XML 1.0.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
