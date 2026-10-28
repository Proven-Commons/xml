# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `xml.etree.ElementTree`, expat_2.6.1 (`ET.XMLParser`, which turns namespace processing on, with a `TreeBuilder` that keeps comments and processing instructions)
- Lean tool: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Inputs: 3298
  - every request sent to the tool: the fixed cases, the generated documents, the named rejections, the malformed requests, and two bare parse requests
- Fixed cases passed: 37 of 37
- Generated in-subset documents: 3200
- Generated documents where the tool's canonical print matches the tree and ElementTree agrees on the tree: 3200
- ElementTree tree agreements on generated documents: 3200
- Named rejections rejected by the tool: 49 of 49
- Out of subset disagreements (ElementTree accepts, this slice rejects, by design): 10
  - document type declaration
  - document type declaration with internal subset
  - colon in an attribute name
  - default namespace declaration
  - empty default namespace declaration
  - default namespace declaration, single quotes
  - default namespace declaration after another attribute
  - default namespace declaration on a child element
  - prefixed namespace declaration
  - the XML declaration form
- Malformed requests answered error: 10 of 10
- Bare parse requests answered none: yes
- Failures: 0
