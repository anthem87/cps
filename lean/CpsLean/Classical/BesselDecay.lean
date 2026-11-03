module

public import CpsLean.Bessel
set_option autoImplicit false

/-!
# Decay of `J₀`, as an explicit hypothesis

`BesselDecay`: `|J₀(x)| ≤ C/√|x|` for `|x| ≥ 1`. It is the bound "eventually `≪ |ξ|^{−1/2}`" of
Step 6 of the proof of Theorem 3, which gives the absolute continuity of `μ_a`.
-/

open Real

@[expose] public section

namespace CpsLean

/-- **Decay of the Bessel function `J₀`** [G. N. Watson, *A Treatise on the Theory of Bessel
Functions*, 2nd ed., Cambridge 1944, §7.21, the asymptotic expansion
`J₀(x) = √(2/(πx)) (cos(x − π/4) + O(1/x))`]: there is `C` with `|J₀(x)| ≤ C/√|x|` for every real
`x` with `|x| ≥ 1`, `J₀` being the power series `besselJ0`. An explicit hypothesis, never an
axiom. -/
def BesselDecay : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ |x| → |besselJ0 x| ≤ C / √|x|

end CpsLean
