module

public import CpsLean.LimitDist
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Module.Rat
set_option autoImplicit false

/-!
# Akbary–Ng–Shahabi, Theorem 1.9, as an explicit hypothesis

The Fourier transform of the limiting distribution when the frequencies are linearly independent
over `ℚ` (Kronecker–Weyl). It is used in Step 6 of the proof of Theorem 3(ii), under LI.
-/

open Complex Filter Topology MeasureTheory Finset

@[expose] public section

namespace CpsLean

/-- **Akbary–Ng–Shahabi, Theorem 1.9** [A. Akbary, N. Ng, M. Shahabi, *Limiting distributions of
the classical error terms of prime number theory*, Q. J. Math. 65 (2014), 743–780,
arXiv:1306.1657, Thm. 1.9, case `ℓ = 1`]: under the conditions of Corollary 1.3(a), if the
frequencies `λ_n` are linearly independent over `ℚ` and `μ` is the limiting distribution of `φ`,
then `μ̂(ξ) = ∫ e^{−iξt} dμ(t) = e^{−icξ} Π_{n≥1} J₀(|r_n ξ|)`, the product converging, with
`J₀(z) = ∫_0^1 e^{−iz cos(2πt)} dt`. Stated for strictly increasing frequencies. An explicit
hypothesis, never an axiom. -/
def AnsThm19 : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r → LinearIndependent ℚ lam →
      ∀ μ : ProbabilityMeasure ℝ, HasLimitingDistribution φ μ → ∀ ξ : ℝ,
        Tendsto (fun N : ℕ => cexp (-I * (c : ℂ) * (ξ : ℂ)) *
            ∏ n ∈ range N, ansJ0 ‖r n * (ξ : ℂ)‖) atTop
          (𝓝 (∫ t, cexp (-I * (ξ : ℂ) * (t : ℂ)) ∂(μ : Measure ℝ)))

end CpsLean
