module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
set_option autoImplicit false

/-!
# The prime number theorem, as an explicit hypothesis

`PNT`: `π(x) ∼ x / log x` as `x → ∞`. Mathlib (rev 3e18214) has Chebyshev's bounds but not the
prime number theorem. It is the hypothesis of Theorem 1, Theorem 2 (asymptotic part),
Proposition 2 and Corollary 2.
-/

open Real Filter Asymptotics

@[expose] public section

namespace CpsLean

/-- **Prime number theorem** [J. Hadamard, *Sur la distribution des zéros de la fonction ζ(s) et ses
conséquences arithmétiques*, Bull. SMF 24 (1896); C. de la Vallée Poussin, *Recherches analytiques
sur la théorie des nombres premiers*, Ann. Soc. Sci. Bruxelles 20 (1896); G. H. Hardy, E. M. Wright,
*An Introduction to the Theory of Numbers*, Thm. 6 (§1.8), proved in Ch. 22]: `π(x) ∼ x / log x` as
`x → ∞`, for real `x` (`π(x) = π(⌊x⌋)`), with no error term. An explicit hypothesis, never an
axiom. -/
def PNT : Prop :=
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x / log x)

end CpsLean
