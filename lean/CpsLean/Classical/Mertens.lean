module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
set_option autoImplicit false

/-!
# Mertens' second theorem, as an explicit hypothesis

`Mertens2`: `Σ_{p≤x} 1/p = log log x + B + O(1/log x)`. Remark 1 uses the consequence
`½ Σ_{p≤√x} 1/p = ½ log log x + O(1)`. Mathlib (rev 3e18214) has only the divergence of `Σ 1/p`.
-/

open Real Filter Asymptotics Finset

@[expose] public section

namespace CpsLean

/-- **Mertens' second theorem** [F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*,
J. reine angew. Math. 78 (1874); G. H. Hardy, E. M. Wright, *An Introduction to the Theory of
Numbers*, Thm. 427]: there is a constant `B` with `Σ_{p≤x} 1/p = log log x + B + O(1/log x)` as
`x → ∞`, for real `x`. An explicit hypothesis, never an axiom. -/
def Mertens2 : Prop :=
  ∃ B : ℝ, (fun x : ℝ =>
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p) - log (log x) - B)
    =O[atTop] (fun x : ℝ => 1 / log x)

end CpsLean
