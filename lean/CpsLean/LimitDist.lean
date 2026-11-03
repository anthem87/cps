module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite
set_option autoImplicit false

/-!
# Limiting distributions and the expansions of Akbary–Ng–Shahabi

Definitions only, used to state the theorems of Akbary–Ng–Shahabi [A. Akbary, N. Ng, M. Shahabi,
*Limiting distributions of the classical error terms of prime number theory*, Q. J. Math. 65
(2014), 743–780; arXiv:1306.1657] cited in Steps 5 and 6 of the proof of Theorem 3.

* `HasLimitingDistribution φ μ` (their Definition 1.1, `ℓ = 1`): for every bounded continuous
  `f`, `(1/Y) ∫_0^Y f(φ(y)) dy → ∫ f dμ`.
* `AnsExpansion φ c y₀ λ r`: their (1.6) and (1.7), `φ(y) = c + Re Σ_{λ_n≤X} r_n e^{iλ_n y} + E(y, X)`
  for `y ≥ y₀` with `(1/Y) ∫_{y₀}^Y |E(y, e^Y)|² dy → 0`. The error `E` is the difference, so the
  expansion is a condition on `φ`, `c`, `λ`, `r`. The frequencies `λ_n` are taken strictly
  increasing (equal frequencies are grouped, their coefficients added), `φ` measurable and
  square-integrable on every `[0, Y]`.
* `AnsCond13a λ r`: the condition (1.11) of their Corollary 1.3(a), `r_n ≪ λ_n^{−β}` for some
  `β > ½` and `Σ_{T<λ_n≤T+1} 1 ≪ log T`.
* `ansJ0 z = ∫_0^1 e^{−iz cos(2πt)} dt`, the Bessel function `J₀` in the form of their Theorem 1.9.
-/

open Real Complex Filter Topology MeasureTheory

@[expose] public section

namespace CpsLean

/-- `φ` has the limiting distribution `μ`: `(1/Y) ∫_0^Y f(φ(y)) dy → ∫ f dμ` for every bounded
continuous `f : ℝ → ℝ`. -/
def HasLimitingDistribution (φ : ℝ → ℝ) (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, f (φ y)) atTop
      (𝓝 (∫ t, f t ∂(μ : Measure ℝ)))

/-- The expansion (1.6)–(1.7) of Akbary–Ng–Shahabi, with strictly increasing frequencies. -/
def AnsExpansion (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ) : Prop :=
  Measurable φ ∧ (∀ Y : ℝ, IntegrableOn (fun y => φ y ^ 2) (Set.Icc 0 Y)) ∧ 0 ≤ y₀ ∧
    StrictMono lam ∧ (∀ n, 0 < lam n) ∧ Tendsto lam atTop atTop ∧
    Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in y₀..Y,
      (φ y - c - (∑ᶠ n ∈ {n : ℕ | lam n ≤ Real.exp Y}, r n * cexp (I * (lam n : ℂ) * (y : ℂ))).re) ^ 2)
      atTop (𝓝 0)

/-- The condition (1.11) of Corollary 1.3(a) of Akbary–Ng–Shahabi. -/
def AnsCond13a (lam : ℕ → ℝ) (r : ℕ → ℂ) : Prop :=
  (∃ β : ℝ, 1 / 2 < β ∧ ∃ C : ℝ, ∀ n, ‖r n‖ ≤ C * lam n ^ (-β)) ∧
    ∃ C : ℝ, ∀ᶠ T in atTop, (Nat.card {n : ℕ | T < lam n ∧ lam n ≤ T + 1} : ℝ) ≤ C * Real.log T

/-- `J₀(z) = ∫_0^1 e^{−iz cos(2πt)} dt`. -/
noncomputable def ansJ0 (z : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, cexp (-I * (z : ℂ) * (Real.cos (2 * π * t) : ℂ))

end CpsLean
