module

public import CpsLean.LimitDist
set_option autoImplicit false

/-!
# Akbary–Ng–Shahabi, Corollary 1.3(a), as an explicit hypothesis

It gives the limiting distribution `μ_a` of `E_a(e^y)` in Step 5 of the proof of Theorem 3(i).
-/

@[expose] public section

namespace CpsLean

/-- **Akbary–Ng–Shahabi, Corollary 1.3(a)** [A. Akbary, N. Ng, M. Shahabi, *Limiting distributions
of the classical error terms of prime number theory*, Q. J. Math. 65 (2014), 743–780,
arXiv:1306.1657, Thm. 1.2 and Cor. 1.3(a)]: if `φ` has an expansion (1.6)–(1.7) with
`r_n ≪ λ_n^{−β}` for some `β > ½` and `Σ_{T<λ_n≤T+1} 1 ≪ log T`, then `φ` is `B²`-almost periodic
and has a limiting distribution. Stated for strictly increasing frequencies. An explicit
hypothesis, never an axiom. -/
def AnsCor13a : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r →
      ∃ μ : MeasureTheory.ProbabilityMeasure ℝ, HasLimitingDistribution φ μ

end CpsLean
