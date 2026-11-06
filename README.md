# CPS

Lean 4 / Mathlib formalization of the paper *Cumulative Prime Sums and Riemann Zeros: a fine grid,
its ripple, and a family of prime races* (A. Mennillo, version 4, Zenodo, November 2026,
DOI [10.5281/zenodo.23962478](https://doi.org/10.5281/zenodo.23962478)).

**No `sorry`.** The Lean project builds with no `sorry` and depends only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). `lean/MainTheorems.lean` states each main result of the
paper and proves it from the library; from `lean/`: `lake env lean Axioms.lean` prints the axioms of each one.

Work in progress. The Lean project is in `lean/` (Lean v4.36.0-rc2, Mathlib
`3e1821461a4bc54072a3bd970e5a2ea5d9fd9713`).

| Path | Content |
|---|---|
| `lean/CpsLean/` | the library |
| `lean/MainTheorems.lean` | the index of the paper's main results, each proved from the library |
| `lean/Axioms.lean` | `#print axioms` of each main theorem (not a default target) |
| `lean/docs/` | derivations written before the Lean code |
| `DIVERGENZE.md` | every difference between a Lean statement and the paper (version 3), side by side |

Published theorems enter as explicit hypotheses (`def … : Prop`), never as axioms; numerical
certificates likewise, each with its script.
The only `set_option maxHeartbeats 1000000` is on `step4_assembling` (`lean/CpsLean/Step4.lean`): its long
assembly of Lemma A and Steps 2 and 3 exceeds the default limit of 200000 heartbeats.

Build: from `lean/`, `lake build`. Common definitions come from
[lean-base](https://github.com/anthem87/lean-base).

## AI use

AI tools were used to assist with computations, the drafting of text and the checking of proofs.
All results were verified by the author, who takes full responsibility for the content.

## License

AGPL-3.0-or-later. The file `LICENSE` is the text of the GNU Affero General Public License,
version 3; you may use this work under version 3 or any later version.
