# Selected statement and edition

The authority is the supplied standalone `proposition-5-3-n3.tex`, Proposition 5.3, label `angular:coercivity`, lines 478–493. The proof begins at line 495. The selected TeX file is preserved byte for byte here (SHA256 `6f3b7ec11a73af85ddac5d65131ac1c88b540acff54ac8b04256a1d5ecb1627b`). Its original supplied archive has SHA256 `911c90c4d9a0c8c9bae977c67963f58f34bbcc072c216d1896fdd7f0cb3f727c`.

`Reference.lean` is the independently preserved approved translation, including the definitions that determine the theorem's meaning and the intentionally open challenge proof. `ComparatorChallenges/Proposition53.lean` is an exact copy. Nothing in the solution imports either file.

The solution retains the original `Fin 9` smallness convention and arbitrary admitted metrics, frames and radius profiles. No additional analytic estimate is a parameter of `ShrinkingSpheres.coercivity`.

Run `./check-challenge.sh` to compare both copies and verify the statement, selected text and dependency pin checksums. In the comparator configuration, `definition_names` is deliberately empty: that field permits definition holes, whereas this challenge requires reachable definitions to agree.
