# Package validation

The 2,723 included solution, supporting and consumer sources are byte-identical to the released proof. Their contents and module paths were preserved during packaging. The release passed fresh isolated compilation, exact comparison of its approved statements and defining declarations, its frozen consumer check and fresh Lean kernel replay.

The public package was additionally checked with the same pinned toolchain and upstream Lake comparator used by the reference repository.

| Check | Result |
| --- | --- |
| `./check-challenge.sh` | PASS: independent statement, selected text and dependency pins agree |
| `lake query --json +Consumer:transImports` | PASS: all 2,723 local solution modules resolve; the challenge is absent from that import graph |
| `lake env lean -j1 Check.lean` | PASS: theorem, closed physical comparison and consumer use only the standard three axioms |
| Upstream `lake comparator`, including fresh kernel replay | PASS: `Your solution is okay!` |
| Local documentation links | PASS |
| Released Lean source hashes | PASS: all 2,723 unchanged |

For package-specific validation, existing compiled artifacts of the unchanged released sources and the pinned dependency cache were reused. The independent public challenge was compiled and exported afresh. The stock comparator was run with its supported `--challenge-from-export` and `--solution-from-export` options: it compared the independent challenge, checked the permitted axioms and replayed the complete solution export in the Lean kernel. Kernel replay was not skipped. A second full clean compilation of the unchanged proof was not performed solely for packaging.

From a new checkout, follow the README's ordinary build and comparator commands. They create fresh local artifacts from the included sources; the package needs no private workflow or pre-existing project directories.

The comparator configuration has an empty `definition_names` list, matching the reference setup. This permits no definition holes; definitions reachable from the selected theorem must agree with the independent challenge.

The source archive contains no compiled objects, NDJSON exports, dependency caches, private workflow databases, review administration or chat metadata. `SHA256SUMS` identifies its public files.
