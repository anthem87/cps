module

public import CpsLean.Zeros
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Module.Rat
set_option autoImplicit false

/-!
# The linear independence hypothesis LI

`LI`: the positive ordinates of the zeros of `ζ` are simple and linearly independent over `ℚ`. It
is a conjecture, used only as the antecedent of Theorem 3(ii) and Theorem 4.
-/

@[expose] public section

namespace CpsLean

/-- **Linear independence hypothesis** (conjecture) [A. Wintner (1935); M. Rubinstein, P. Sarnak,
*Chebyshev's bias*, Experiment. Math. 3 (1994), §1]: the positive ordinates `γ` of the nontrivial
zeros of `ζ`, counted with multiplicity, are linearly independent over `ℚ`. With multiplicity this
says three things: every nontrivial zero with `γ > 0` is simple, no two of them have the same
ordinate, and the distinct ordinates are linearly independent over `ℚ`. This form implies RH: an
off-line zero `ρ` and its twin `1 − ρ̄` share the ordinate. Rubinstein–Sarnak state LI under RH;
here it is only used together with `RiemannHypothesis`. A conjecture, used only as an antecedent;
never an axiom. -/
def LI : Prop :=
  (∀ ρ ∈ nontrivialZeros, 0 < ρ.im → zeroMult ρ = 1) ∧
    (∀ ρ₁ ∈ nontrivialZeros, ∀ ρ₂ ∈ nontrivialZeros, 0 < ρ₁.im → ρ₁.im = ρ₂.im → ρ₁ = ρ₂) ∧
    LinearIndependent ℚ (fun γ : zeroOrdinates => (γ : ℝ))

end CpsLean
