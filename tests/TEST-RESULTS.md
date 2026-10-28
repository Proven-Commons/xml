# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `xml.etree.ElementTree` (expat), subset mode as described in the harness
- Lean tool: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261026
- Fixed cases passed: 35 of 35
- Generated in-subset documents: 3200
- Generated documents where the tool's canonical print matches the tree and ElementTree agrees on the tree: 3200
- ElementTree tree agreements on generated documents: 3200
- Named rejections rejected by the tool: 43 of 43
- Out of subset disagreements (ElementTree accepts, this slice rejects, by design): 4
  - document type declaration
  - document type declaration with internal subset
  - colon in an attribute name
  - the XML declaration form
- Malformed requests answered error: 10 of 10
- Bare parse requests answered none: yes
- Failures: 0
