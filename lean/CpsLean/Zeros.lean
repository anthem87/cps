module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Algebra.BigOperators.Finprod
set_option autoImplicit false

/-!
# The nontrivial zeros of `ζ`, counted with multiplicity

Definitions only, used to state the classical hypotheses of Lemma A, Theorem 3 and Theorem 4.

* `nontrivialZeros`: the zeros `ρ = β + iγ` of `ζ` with `0 < β < 1`.
* `zeroMult ρ`: the multiplicity of `ρ`, the order of vanishing of `ζ` at `ρ`.
* `zeroSumLe T f = Σ_{|γ| ≤ T} f(ρ)` (the truncation of the paper) and `zeroSumLt T f = Σ_{|γ| < T} f(ρ)`
  (that of Davenport), each zero counted with its multiplicity. The sets are finite (the zeros of
  `ζ` are discrete, `IsCompact.inter_riemannZetaZeros_finite`), so the finite sums `∑ᶠ` are the sums
  of the paper.
* `zeroCount T = N(T)`, the number of nontrivial zeros with `0 < γ ≤ T`, with multiplicity.
* `zeroOrdinates`: the set of positive ordinates `γ` (each one once).
* `psi0 x = ψ₀(x)`: `ψ(x)` with the value at a jump replaced by the mean of the two one-sided
  limits, `ψ(x) − Λ(x)/2` at an integer `x`.
* `primePowerDist x = ⟨x⟩`: the distance from `x` to the nearest prime power other than `x`.
-/

open Real Complex

@[expose] public section

namespace CpsLean

/-- The nontrivial zeros of `ζ`: `ζ(ρ) = 0` and `0 < Re ρ < 1`. -/
def nontrivialZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The multiplicity of a zero `ρ` of `ζ`: the order of vanishing of `ζ` at `ρ`. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- `Σ_{|γ| ≤ T} f(ρ)` over the nontrivial zeros `ρ = β + iγ`, with multiplicity. -/
noncomputable def zeroSumLe (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ |ρ.im| ≤ T}, (zeroMult ρ : ℂ) * f ρ

/-- `Σ_{|γ| < T} f(ρ)` over the nontrivial zeros `ρ = β + iγ`, with multiplicity. -/
noncomputable def zeroSumLt (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ |ρ.im| < T}, (zeroMult ρ : ℂ) * f ρ

/-- `N(T)`: the number of nontrivial zeros with `0 < γ ≤ T`, with multiplicity. -/
noncomputable def zeroCount (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T}, zeroMult ρ

/-- The positive ordinates `γ > 0` of the nontrivial zeros, each one once. -/
def zeroOrdinates : Set ℝ := {γ | 0 < γ ∧ ∃ ρ ∈ nontrivialZeros, ρ.im = γ}

/-- `ψ₀(x)`: `ψ(x) − Λ(x)/2` when `x` is an integer, `ψ(x)` otherwise. -/
noncomputable def psi0 (x : ℝ) : ℝ :=
  Chebyshev.psi x -
    if (⌊x⌋₊ : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0

/-- `⟨x⟩`: the distance from `x` to the nearest prime power other than `x`. -/
noncomputable def primePowerDist (x : ℝ) : ℝ :=
  ⨅ n : {n : ℕ // IsPrimePow n ∧ (n : ℝ) ≠ x}, |x - (n : ℝ)|

end CpsLean
