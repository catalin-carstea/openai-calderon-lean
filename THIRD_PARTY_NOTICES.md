# Third-party code and attribution

The project authors are Cătălin I. Cârstea and Lauri Oksanen. Original project contributions are distributed under the BSD 3-Clause License. The proof also includes AI-assisted development. Upstream code retains its copyright and license terms. [Project license](LICENSE)

## Tau Ceti

The 109 Lean files under `Proof/ReleasedAnalysis/TauCeti/` and `Proof/PriorAnalysis/TauCeti/` are bundled Tau Ceti code, including adaptations from the earlier Calderón work and the conformal Poisson package. Their copyright and author notices are preserved in the sources. The earlier Calderón work uses Tau Ceti revision `d87e7f1676050bccc88913a473d5aae77156313c`. The conformal Poisson source lock records revision `4d91513e4d30746eb1fa96658c18e051c772e55e`. The vendored sources include import changes and adapted results. [Tau Ceti](https://github.com/TauCetiProject/TauCeti) · [Apache License, Version 2.0](licenses/TauCeti-Apache-2.0.txt) · [Vendored source checksums](docs/provenance/checked-sources.json)

The almost-everywhere finite union integration result in `Bochner/Basic.lean` includes the retained attribution to AINTLIB's LeanModularForms project at `6d87d596a5372d5b122c47b7082d4c3afa9b7c3b`, under Apache 2.0. [Source notice](Proof/ReleasedAnalysis/TauCeti/MeasureTheory/Integral/Bochner/Basic.lean#L173)

## Conformal Poisson formalization

The half-space trace and regularity results and parts of the boundary-layer construction adapt code from Cătălin I. Cârstea, Tony Liimatainen, Yi-Hsuan Lin, and William Trad's Lean formalization at `4cfcab036aedbb4f825a3aeb366da12fe5673ddd`. The per-file adoption ledger records the original modules or extracted components and their adaptations. [Pinned upstream](https://github.com/catalin-carstea/arxiv-2610.13592-lean/tree/4cfcab036aedbb4f825a3aeb366da12fe5673ddd) · [Conformal Poisson license](licenses/ConformalPoisson-BSD-3-Clause.txt) · [Source lock](docs/provenance/conformal-poisson-source-lock.json) · [Adoption ledger](docs/provenance/conformal-poisson-adoptions.json)

## Mathematical source and dependencies

OpenAI authored the source manuscript. Lean, Mathlib, and the other pinned packages are maintained by their respective contributors and supply their own licenses. [Selected edition](docs/statement/README.md) · [Lean toolchain](lean-toolchain) · [Package revisions](lake-manifest.json)
