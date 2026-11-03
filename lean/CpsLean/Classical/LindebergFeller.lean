module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option autoImplicit false

/-!
# The central limit theorem of Lindeberg, as an explicit hypothesis

For triangular arrays of independent centred variables with total variance `1`, the Lindeberg
condition gives convergence in law to `N(0, 1)`. It is used in the proof of Theorem 4(a).
Mathlib (rev 3e18214) has the central limit theorem only for i.i.d. variables.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

@[expose] public section

namespace CpsLean

/-- **Lindeberg's central limit theorem** [J. W. Lindeberg, *Eine neue Herleitung des
Exponentialgesetzes in der Wahrscheinlichkeitsrechnung*, Math. Z. 15 (1922); P. Billingsley,
*Probability and Measure*, 3rd ed., Thm. 27.2]: let, for each `n`, `X_{n,0}, …, X_{n,k_n−1}` be
independent real random variables on a probability space `(Ω_n, P_n)`, square-integrable, centred,
with `Σ_j E[X_{n,j}²] = 1`; if for every `ε > 0`, `Σ_j E[X_{n,j}²; |X_{n,j}| > ε] → 0`, then
`Σ_j X_{n,j}` converges in law to `N(0, 1)`. An explicit hypothesis, never an axiom. -/
def LindebergFeller : Prop :=
  ∀ (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (k : ℕ → ℕ) (X : ∀ n, ℕ → Ω n → ℝ),
    (∀ n, iIndepFun (fun j : Fin (k n) => X n j) (P n)) →
    (∀ n j, MemLp (X n j) 2 (P n)) →
    (∀ n j, ∫ ω, X n j ω ∂(P n) = 0) →
    (∀ n, ∑ j ∈ range (k n), ∫ ω, X n j ω ^ 2 ∂(P n) = 1) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => ∑ j ∈ range (k n),
        ∫ ω, Set.indicator {ω | ε < |X n j ω|} (fun ω => X n j ω ^ 2) ω ∂(P n)) atTop (𝓝 0)) →
    TendstoInDistribution (fun n ω => ∑ j ∈ range (k n), X n j ω) atTop id P (gaussianReal 0 1)

end CpsLean
