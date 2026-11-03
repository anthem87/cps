module

public import CpsLean.LimitDist
set_option autoImplicit false

/-!
# Akbary–Ng–Shahabi, Theorem 1.14, as an explicit hypothesis

The mean square of `φ`. It bounds the second moments in Step 5 of the proof of Theorem 3(i), where
the mean of `μ_a` is computed.
-/

open Filter Topology

@[expose] public section

namespace CpsLean

/-- **Akbary–Ng–Shahabi, Theorem 1.14** [A. Akbary, N. Ng, M. Shahabi, *Limiting distributions of
the classical error terms of prime number theory*, Q. J. Math. 65 (2014), 743–780,
arXiv:1306.1657, Thm. 1.14, from Besicovitch's Parseval identity]: under the conditions of
Corollary 1.3(a), `(1/Y) ∫_0^Y φ(y)² dy → c² + ½ Σ_n |r_n|²`. Stated for strictly increasing
frequencies (the formula as printed needs distinct `λ_n`). An explicit hypothesis, never an
axiom. -/
def AnsThm114 : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r →
      Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, φ y ^ 2) atTop
        (𝓝 (c ^ 2 + 1 / 2 * ∑' n, ‖r n‖ ^ 2))

end CpsLean
