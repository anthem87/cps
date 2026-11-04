module

public import Mathlib
public import CpsLean

set_option autoImplicit false

/-!
# Solution

The text of `Challenge.lean` (definitions in the namespace `CPS`, copied from the library
`CpsLean`), with each proof given by the corresponding theorem of `CpsLean`: the
`CPS` definitions are the `CpsLean` ones, so the statements agree by unfolding.
-/

set_option maxHeartbeats 4000000

@[expose] public section

section
open Finset Real
namespace CPS
/-- `p_m`, the `m`-th prime, with `p₁ = 2` (Definition 1). -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)
/-- `S_N = 1 + Σ_{p ≤ N} p` (Definition 1). -/
def S (N : ℕ) : ℕ := 1 + ∑ q ∈ (range (N + 1)).filter Nat.Prime, q
/-- `σ_m = log S_{p_m}` (Definition 1). -/
noncomputable def sigma (m : ℕ) : ℝ := log (S (prime m))
/-- The step `Δ_m = σ_{m+1} − σ_m` (Section 3). -/
noncomputable def step (m : ℕ) : ℝ := sigma (m + 1) - sigma m
/-- The first-crossing prime `N(t) = min{p prime : log S_p ≥ t}` (Definition 2, for `t ≥ log 3`). -/
noncomputable def firstCrossing (t : ℝ) : ℕ := sInf {p : ℕ | p.Prime ∧ t ≤ log (S p)}
/-- `ε(t) = log S_{N(t)} − t` (Definition 2). -/
noncomputable def eps (t : ℝ) : ℝ := log (S (firstCrossing t)) - t
/-- `m(t)`, the index of the first-crossing prime: `p_{m(t)} = N(t)` (Section 3). -/
noncomputable def cellIndex (t : ℝ) : ℕ := Nat.primeCounting (firstCrossing t)
/-- The width of the cell containing `t`, `δ(t) = σ_{m(t)} − σ_{m(t)−1}` (Section 3). -/
noncomputable def cell (t : ℝ) : ℝ := sigma (cellIndex t) - sigma (cellIndex t - 1)
/-- **Definition 1.** `(σ_m)` is strictly increasing and `σ₁ = log 3`. -/
theorem _root_.CPS.def1_sigma : (∀ m n : ℕ, 1 ≤ m → m < n → sigma m < sigma n) ∧ sigma 1 = log 3 := by
  with_unfolding_all exact CpsLean.def1_sigma
/-- **Proposition 1** (in the reading of its proof, see DIVERGENZE.md, D1). -/
theorem _root_.CPS.prop1_crossing_prime {t : ℝ} (ht : log 3 ≤ t) :
    firstCrossing t = sInf {N : ℕ | 1 ≤ N ∧ t ≤ log (S N)} ∧ (firstCrossing t).Prime := by
  with_unfolding_all exact CpsLean.prop1_crossing_prime (t := t) ht
/-- **Theorem 2** (Covering Theorem), the part that does not use the prime number theorem: `S_{p_m} ≥ p_{m+1}` for `m ≥ 1`; `Δ_m ≤ log 2`, with … -/
theorem _root_.CPS.theorem2_covering :
    (∀ m : ℕ, 1 ≤ m → prime (m + 1) ≤ S (prime m)) ∧
      (∀ m : ℕ, 1 ≤ m → step m ≤ log 2 ∧ (step m = log 2 ↔ m = 1)) ∧
      eps (log 3) = 0 ∧
      (∀ t : ℝ, log 3 < t → 0 ≤ eps t ∧ eps t < cell t ∧ cell t ≤ log 2) := by
  with_unfolding_all exact CpsLean.theorem2_covering
/-- `{1} ∪ {q prime : q ≤ p_m}`: the elements `1, 2, 3, 5, …, p_m`. -/
def gridSet (N : ℕ) : Finset ℕ := insert 1 ((range (N + 1)).filter Nat.Prime)
/-- **Remark (Brown's criterion), after Theorem 2.** For `m ≥ 1`, `p_{m+1} ≤ S_{p_m} + 1` (Brown's criterion for `1, 2, 3, 5, …`), and every integer … -/
theorem _root_.CPS.brown_remark {m : ℕ} (hm : 1 ≤ m) :
    prime (m + 1) ≤ S (prime m) + 1 ∧
      ∀ T : ℕ, 1 ≤ T → T ≤ S (prime m) → ∃ A ⊆ gridSet (prime m), ∑ a ∈ A, a = T := by
  with_unfolding_all exact CpsLean.brown_remark (m := m) hm
end CPS
end
section
open Finset Real Filter Asymptotics MeasureTheory
namespace CPS
/-- `S(x) = 1 + Σ_{p ≤ x} p` for real `x` (Section 8.1). -/
noncomputable def Sx (x : ℝ) : ℝ := S ⌊x⌋₊
/-- The mean curve `B(x) = 1 + li(x²) − li(4)` (Section 8.1), with `li(x²) − li(4) = ∫_4^{x²} du/log u`. -/
noncomputable def B (x : ℝ) : ℝ := 1 + ∫ u in (4 : ℝ)..x ^ 2, 1 / log u
/-- **Proposition 3(b).** If `S(x) − B(x) = O(x^{3/2+ε})` for every `ε > 0`, then the Riemann hypothesis holds. -/
theorem _root_.CPS.prop3b_ripple_imp_RH
    (h : ∀ ε : ℝ, 0 < ε → (fun x : ℝ => Sx x - B x) =O[atTop] (fun x : ℝ => x ^ ((3 : ℝ) / 2 + ε))) :
    RiemannHypothesis := by
  with_unfolding_all exact CpsLean.prop3b_ripple_imp_RH h
end CPS
end
section
open Finset Real Filter Topology Nat
namespace CPS
/-- The Bessel function `J₀(x) = Σ_{k≥0} (−1)^k (x/2)^{2k} / (k!)²`. -/
noncomputable def besselJ0 (x : ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * (x / 2) ^ (2 * k) / ((k ! : ℝ) ^ 2)
end CPS
end
section
open Real Filter Asymptotics
namespace CPS
/-- **Prime number theorem** (Hadamard, de la Vallée Poussin 1896; Hardy–Wright, Thm. 6): `π(x) ∼ x / log x` as `x → ∞`. An explicit hypothesis, never an axiom. -/
def PNT : Prop :=
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x / log x)
end CPS
end
section
open Finset Real Filter Topology Asymptotics
namespace CPS
/-- **Theorem 1(i)** (Step Theorem). -/
theorem _root_.CPS.theorem1_i (hP : PNT) : step ~[atTop] (fun m : ℕ => 2 / (m : ℝ)) := by
  with_unfolding_all exact CpsLean.theorem1_i hP
/-- **Proposition 2** (Scaling law). -/
theorem _root_.CPS.prop2_scaling (hP : PNT) :
    Tendsto (fun t => t - (2 * log (firstCrossing t : ℝ) - log (log (firstCrossing t : ℝ)) - log 2))
      atTop (𝓝 0) := by
  with_unfolding_all exact CpsLean.prop2_scaling hP
/-- **Theorem 1(ii)** (Step Theorem), and the asymptotics of Theorem 2: `δ(t) = (1 + o(1)) √t e^{−t/2}`. -/
theorem _root_.CPS.theorem1_ii (hP : PNT) : cell ~[atTop] (fun t => √t * exp (-(t / 2))) := by
  with_unfolding_all exact CpsLean.theorem1_ii hP
/-- **Theorem 2, asymptotic part.** `δ(t) = (1 + o(1)) √t e^{−t/2}`; a restatement of Theorem 1(ii). -/
theorem _root_.CPS.theorem2_asymp (hP : PNT) : cell ~[atTop] (fun t => √t * exp (-(t / 2))) := by
  with_unfolding_all exact CpsLean.theorem2_asymp hP
/-- **Corollary 2** (Half-exponent law, corrected form). -/
theorem _root_.CPS.cor2_halfExponent (hP : PNT) :
    ((fun t => (firstCrossing t : ℝ)) ~[atTop] (fun t => √t * exp (t / 2))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t t' : ℝ, T ≤ t → t ≤ t' →
        |(firstCrossing t' : ℝ) / firstCrossing t / (exp ((t' - t) / 2) * √(t' / t)) - 1| < ε := by
  with_unfolding_all exact CpsLean.cor2_halfExponent hP
end CPS
end
section
open Real Filter Asymptotics
namespace CPS
open scoped Nat.Prime
/-- **von Koch's theorem, form with `ψ`** (von Koch 1901; Davenport, Ch. 18; Montgomery–Vaughan, Thm. 13.1): under the Riemann hypothesis, `ψ(x) = x + O(√x log² x)` as `x → ∞`. An explicit hypothesis, never an axiom. -/
def VonKochPsi : Prop :=
  RiemannHypothesis →
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => √x * log x ^ 2)
end CPS
end
section
open Finset Real Filter Topology Asymptotics MeasureTheory Set
namespace CPS
/-- `θ_b(y) = Σ_{p ≤ y} p^b` (Section 9.2), for real `b`. -/
noncomputable def thetaPow (b y : ℝ) : ℝ := ∑ p ∈ (Finset.Icc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ b
/-- **Proposition 3(a).** Under the Riemann hypothesis (with von Koch's theorem), `S(x) − B(x) = O(x^{3/2} log x)`, hence `|log S(x) − log B(x)| = … -/
theorem _root_.CPS.prop3a_RH_imp_ripple (hK : CPS.VonKochPsi) (hRH : RiemannHypothesis) :
    ((fun x : ℝ => Sx x - B x) =O[atTop] (fun x : ℝ => x ^ ((3 : ℝ) / 2) * log x)) ∧
      ((fun x : ℝ => log (Sx x) - log (B x)) =O[atTop] (fun x : ℝ => log x ^ 2 / √x)) := by
  with_unfolding_all exact CpsLean.prop3a_RH_imp_ripple hK hRH
end CPS
end
section
open Finset Real Filter Topology Asymptotics MeasureTheory Set
namespace CPS
/-- **Theorem 3, Step 2** (the layer `k = 2`, source of the bias). -/
theorem _root_.CPS.step2_bias_layer (hK : CPS.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    (fun x : ℝ => (1 / 2) * thetaPow (2 * a) (√x) - x ^ (a + 1 / 2) / ((2 * a + 1) * log x))
      =O[atTop] (fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x) / log x) := by
  with_unfolding_all exact CpsLean.step2_bias_layer hK hRH (a := a) ha
end CPS
end
section
open Real Complex
namespace CPS
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
end CPS
end
section
open Real Complex Filter Topology MeasureTheory
namespace CPS
/-- `φ` has the limiting distribution `μ`: `(1/Y) ∫_0^Y f(φ(y)) dy → ∫ f dμ` for every bounded continuous `f : ℝ → ℝ`. -/
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
end CPS
end
section
open Real
namespace CPS
/-- **Truncated explicit formula for `ψ`** (Montgomery–Vaughan, *MNT I*, Thm. 12.5, p. 400, https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/16.0_pp_397_418_Explicit_formulae.pdf; Davenport, Ch. 17): there is a constant `C` such that, for every real `x ≥ 2` and `T ≥ 2`, `|ψ₀(x) − (x − Σ_{|γ|<T} x^ρ/ρ − ζ′(0)/ζ(0) − ½ log(1 − x^{−2}))| ≤ C (x log²(xT)/T + log x · min(1, x/(T⟨x⟩)))`. The Lean form (x ≥ 2, |γ| < T) follows from it: the zeros with |γ| = T are ≪ log T and contribute ≪ x log T / T. An explicit hypothesis, never an axiom. -/
def TruncatedExplicitFormula : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖((psi0 x : ℝ) : ℂ) - ((x : ℂ) - zeroSumLt T (fun ρ => (x : ℂ) ^ ρ / ρ)
        - deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ))‖ ≤
      C * (x * log (x * T) ^ 2 / T + log x * min 1 (x / (T * primePowerDist x)))
end CPS
end
section
open Real Filter Asymptotics
namespace CPS
/-- **Riemann–von Mangoldt formula** (von Mangoldt 1905; Davenport, Ch. 15): the number `N(T)` of nontrivial zeros with `0 < γ ≤ T`, counted with multiplicity, is `(T/2π) log(T/2π) − T/2π + O(log T)` as `T → ∞`. An explicit hypothesis, never an axiom. -/
def RiemannVonMangoldt : Prop :=
  (fun T : ℝ => (zeroCount T : ℝ) - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π)))
    =O[atTop] (fun T : ℝ => log T)
end CPS
end
namespace CPS
/-- **Linear independence hypothesis** (conjecture; Wintner 1935; Rubinstein–Sarnak, *Chebyshev's bias*, §1): the positive ordinates `γ` of the nontrivial zeros of `ζ`, counted with multiplicity, are linearly independent over `ℚ`. With multiplicity this says three things: every nontrivial zero with `γ > 0` is simple, no two of them have the same ordinate, and the distinct ordinates are linearly independent over `ℚ`. A conjecture, used only as an antecedent; never an axiom. -/
def LI : Prop :=
  (∀ ρ ∈ nontrivialZeros, 0 < ρ.im → zeroMult ρ = 1) ∧
    (∀ ρ₁ ∈ nontrivialZeros, ∀ ρ₂ ∈ nontrivialZeros, 0 < ρ₁.im → ρ₁.im = ρ₂.im → ρ₁ = ρ₂) ∧
    LinearIndependent ℚ (fun γ : zeroOrdinates => (γ : ℝ))
end CPS
section
open Real Filter Asymptotics Finset
namespace CPS
/-- **Mertens' second theorem** (Mertens 1874; Hardy–Wright, Thm. 427): there is a constant `B` with `Σ_{p≤x} 1/p = log log x + B + O(1/log x)` as `x → ∞`, for real `x`. An explicit hypothesis, never an axiom. -/
def Mertens2 : Prop :=
  ∃ B : ℝ, (fun x : ℝ =>
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p) - log (log x) - B)
    =O[atTop] (fun x : ℝ => 1 / log x)
end CPS
end
section
open Real
namespace CPS
/-- **Decay of the Bessel function `J₀`** (Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., §7.21): there is `C` with `|J₀(x)| ≤ C/√|x|` for every real `x` with `|x| ≥ 1`, `J₀` being the power series `besselJ0`. An explicit hypothesis, never an axiom. -/
def BesselDecay : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ |x| → |besselJ0 x| ≤ C / √|x|
end CPS
end
namespace CPS
/-- **Akbary–Ng–Shahabi, Corollary 1.3(a)** (Q. J. Math. 65 (2014), arXiv:1306.1657, Thm. 1.2 and Cor. 1.3(a)): if `φ` has an expansion (1.6)–(1.7) with `r_n ≪ λ_n^{−β}` for some `β > ½` and `Σ_{T<λ_n≤T+1} 1 ≪ log T`, then `φ` has a limiting distribution. Stated for strictly increasing frequencies. An explicit hypothesis, never an axiom. -/
def AnsCor13a : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r →
      ∃ μ : MeasureTheory.ProbabilityMeasure ℝ, HasLimitingDistribution φ μ
end CPS
section
open Complex Filter Topology MeasureTheory Finset
namespace CPS
/-- **Akbary–Ng–Shahabi, Theorem 1.9** (Q. J. Math. 65 (2014), arXiv:1306.1657, case `ℓ = 1`): under the conditions of Corollary 1.3(a), if the frequencies `λ_n` are linearly independent over `ℚ` and `μ` is the limiting distribution of `φ`, then `∫ e^{−iξt} dμ(t) = e^{−icξ} Π_{n≥1} J₀(|r_n ξ|)`, the product converging, with `J₀(z) = ∫_0^1 e^{−iz cos(2πt)} dt`. Stated for strictly increasing frequencies. An explicit hypothesis, never an axiom. -/
def AnsThm19 : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r → LinearIndependent ℚ lam →
      ∀ μ : ProbabilityMeasure ℝ, HasLimitingDistribution φ μ → ∀ ξ : ℝ,
        Tendsto (fun N : ℕ => cexp (-I * (c : ℂ) * (ξ : ℂ)) *
            ∏ n ∈ range N, ansJ0 ‖r n * (ξ : ℂ)‖) atTop
          (𝓝 (∫ t, cexp (-I * (ξ : ℂ) * (t : ℂ)) ∂(μ : Measure ℝ)))
end CPS
end
section
open Filter Topology
namespace CPS
/-- **Akbary–Ng–Shahabi, Theorem 1.14** (Q. J. Math. 65 (2014), arXiv:1306.1657): under the conditions of Corollary 1.3(a), `(1/Y) ∫_0^Y φ(y)² dy → c² + ½ Σ_n |r_n|²`. Stated for strictly increasing frequencies (the formula as printed needs distinct `λ_n`). An explicit hypothesis, never an axiom. -/
def AnsThm114 : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r →
      Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, φ y ^ 2) atTop
        (𝓝 (c ^ 2 + 1 / 2 * ∑' n, ‖r n‖ ^ 2))
end CPS
end
section
open Real MeasureTheory Set
namespace CPS
/-- **Inversion formula** (Rubinstein–Sarnak, *Chebyshev's bias*, §3; Gil-Pelaez 1951): if `ν` is a probability measure on `ℝ`, symmetric about `0`, whose characteristic function `φ̂(ξ) = ∫ e^{iξt} dν(t)` (real, by symmetry) is integrable, then for every `b > 0`, `ν((b, ∞)) = ½ − (1/π) ∫_0^∞ sin(bξ)/ξ · φ̂(ξ) dξ`. An explicit hypothesis, never an axiom. -/
def RubinsteinSarnakInversion : Prop :=
  ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ).map (fun t => -t) = ν →
    Integrable (charFun (ν : Measure ℝ)) → ∀ b : ℝ, 0 < b →
      (ν : Measure ℝ).real (Ioi b) =
        1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (b * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re
end CPS
end
section
open Real Filter Topology MeasureTheory Set
namespace CPS
/-- `li(y) = PV ∫_0^y du / log u = lim_{ε→0⁺} (∫_0^{1−ε} + ∫_{1+ε}^y) du / log u`, for `y > 1`. -/
noncomputable def li (y : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => (∫ u in (0 : ℝ)..(1 - ε), 1 / log u) +
    ∫ u in (1 + ε)..y, 1 / log u)
end CPS
end
section
open Finset Real Filter Topology Asymptotics MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt
namespace CPS
/-- `Π_a(x) = Σ_{p^k ≤ x} p^{ka}/k`, written with `Λ(p^k)/log(p^k) = 1/k`. -/
noncomputable def piA (a x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ a / log n * Λ n
end CPS
end
section
open Finset Real Filter Topology Asymptotics MeasureTheory Set
namespace CPS
/-- **Lemma A** (pointwise form of the layer `k = 1`). Assume RH. For `a > −½`, `Y ≥ 2`, `T = e^Y` and `3 ≤ x ≤ e^Y`, `Π_a(x) = li(x^{a+1}) − (x^κ/log x) Σ_{|γ|≤T} x^{iγ}/(ρ + a) + O_a(x^κ/log² x + Y² e^{−Y/2} x^κ/log x + 1)`, with `κ = a + ½`. -/
theorem _root_.CPS.lemmaA (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, ∀ Y x : ℝ, 2 ≤ Y → 3 ≤ x → x ≤ exp Y →
      ‖((piA a x : ℝ) : ℂ) - (((li (x ^ (a + 1)) : ℝ) : ℂ) -
          ((x ^ (a + 1 / 2) / log x : ℝ) : ℂ) *
            zeroSumLe (exp Y) (fun ρ => (x : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ))))‖ ≤
        C * (x ^ (a + 1 / 2) / log x ^ 2 + Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x) + 1) := by
  with_unfolding_all exact CpsLean.lemmaA hE hN hRH (a := a) ha
end CPS
end
section
open Finset Real Filter Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt
namespace CPS
/-- `R(x) = Σ_{k≥3} (1/k) θ_{ka}(x^{1/k})`: for `k > log₂ x` the sum `θ_{ka}(x^{1/k})` is empty. -/
noncomputable def layersR (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 ⌊log x / log 2⌋₊, (1 / (k : ℝ)) * thetaPow (k * a) (x ^ ((1 : ℝ) / k))
/-- **Theorem 3, Step 3** (the layers `k ≥ 3`): for every real `a > −½`, `Σ_{k≥3} (1/k) θ_{ka}(x^{1/k}) = o(x^{a+½}/log x)`. -/
theorem _root_.CPS.step3_layers {a : ℝ} (ha : -1 / 2 < a) :
    (fun x : ℝ => layersR a x) =o[atTop] (fun x : ℝ => x ^ (a + 1 / 2) / log x) := by
  with_unfolding_all exact CpsLean.step3_layers (a := a) ha
end CPS
end
section
open Finset Real Filter Topology Asymptotics
open scoped ComplexConjugate
namespace CPS
/-- `E_a(x) = (θ_a(x) − li(x^{a+1})) log x / x^{a+½}`. -/
noncomputable def errA (a x : ℝ) : ℝ :=
  (thetaPow a x - li (x ^ (a + 1))) * (log x / x ^ (a + 1 / 2))
/-- `Σ_{0<γ≤T} f(ρ)` over the nontrivial zeros `ρ = β + iγ`, with multiplicity. -/
noncomputable def zeroSumPos (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T}, (zeroMult ρ : ℂ) * f ρ
/-- The term of the race: `g(ρ) = e^{iγy}/(½ + a + iγ)`. -/
noncomputable def raceTerm (a y : ℝ) (ρ : ℂ) : ℂ :=
  Complex.exp (Complex.I * (ρ.im : ℂ) * (y : ℂ)) / (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))
/-- **Theorem 3, Step 4** (assembling). Assume RH. For `a > −½`, `Y ≥ 2`, `T = e^Y`, `log 3 ≤ y ≤ Y`, `E_a(e^y) = −1/(2a+1) − 2 Re Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ) + ε_a(y, T)` with `|ε_a(y, T)| ≪_a 1/y + Y² e^{−Y/2}`. -/
theorem _root_.CPS.step4_assembling (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : CPS.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y y : ℝ, 2 ≤ Y → log 3 ≤ y → y ≤ Y →
      |errA a (exp y) - (-1 / (2 * a + 1) - 2 * (zeroSumPos (exp Y) (raceTerm a y)).re)| ≤
        C * (1 / y + Y ^ 2 * exp (-Y / 2)) := by
  with_unfolding_all exact CpsLean.step4_assembling hE hN hK hRH (a := a) ha
end CPS
end
section
open Real Filter Topology MeasureTheory Set Asymptotics
namespace CPS
/-- `φ(y) = E_a(e^y)`, for `y ≥ log 2`, and `0` before. -/
noncomputable def phiA (a y : ℝ) : ℝ := if log 2 ≤ y then errA a (exp y) else 0
/-- **Theorem 3(i)** (Bias law). Assume RH. For every real `a > −½`, `E_a(e^y)` has a limiting logarithmic distribution `μ_a`, and `∫ t dμ_a(t) = −1/(2a+1)`. -/
theorem _root_.CPS.theorem3_i (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : CPS.VonKochPsi) (hC : AnsCor13a) (hP : AnsThm114) (hRH : RiemannHypothesis)
    {a : ℝ} (ha : -1 / 2 < a) :
    ∃ μ : ProbabilityMeasure ℝ, HasLimitingDistribution (phiA a) μ ∧
      Integrable (fun t : ℝ => t) (μ : Measure ℝ) ∧
      ∫ t, t ∂(μ : Measure ℝ) = -1 / (2 * a + 1) := by
  with_unfolding_all exact CpsLean.theorem3_i hE hN hK hC hP hRH (a := a) ha
end CPS
end
section
open Real Filter Topology MeasureTheory Set Finset
namespace CPS
/-- `|½ + a + iγ|`. -/
noncomputable def zeroDen (a γ : ℝ) : ℝ := ‖((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)‖
/-- `Π_{γ>0} J₀(2ξ/|½+a+iγ|)`, over the positive ordinates of the zeros of `ζ`. -/
noncomputable def prodJ (a ξ : ℝ) : ℝ :=
  ∏' γ : zeroOrdinates, besselJ0 (2 * ξ / zeroDen a γ)
end CPS
end
section
open Real Filter Topology MeasureTheory Set ProbabilityTheory
namespace CPS
/-- `δ_a = ½ − (1/π) ∫_0^∞ sin(ξ/(2a+1))/ξ · Π_{γ>0} J₀(2ξ/|½+a+iγ|) dξ`. -/
noncomputable def deltaA (a : ℝ) : ℝ :=
  1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ
/-- `S` has logarithmic density `d`: `(1/log X) ∫_2^X 1_S(x) dx/x → d`. -/
def HasLogDensity (S : Set ℝ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℝ => (1 / log X) * ∫ x in (2 : ℝ)..X, S.indicator (fun x => 1 / x) x) atTop (𝓝 d)
/-- **Theorem 3(ii)** (Bias law). Assume RH and LI. For every real `a > −½`, the limiting distribution `μ_a` of `E_a(e^y)` is absolutely continuous and symmetric about `−1/(2a+1)`, and the logarithmic density of `{x : θ_a(x) > li(x^{a+1})}` exists and equals `δ_a = ½ − (1/π) ∫_0^∞ sin(ξ/(2a+1))/ξ · Π_{γ>0} J₀(2ξ/|½+a+iγ|) dξ`; the product converges and the integrand is integrable. -/
theorem _root_.CPS.theorem3_ii (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : CPS.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI)
    {a : ℝ} (ha : -1 / 2 < a) {μ : ProbabilityMeasure ℝ}
    (hμ : HasLimitingDistribution (phiA a) μ) :
    (μ : Measure ℝ) ≪ volume ∧
    (μ : Measure ℝ).map (fun t => 2 * (-1 / (2 * a + 1)) - t) = μ ∧
    (∀ ξ : ℝ, Multipliable (fun γ : zeroOrdinates => besselJ0 (2 * ξ / zeroDen a γ))) ∧
    IntegrableOn (fun ξ => sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ) (Ioi 0) ∧
    HasLogDensity {x : ℝ | li (x ^ (a + 1)) < thetaPow a x} (deltaA a) := by
  with_unfolding_all exact CpsLean.theorem3_ii hE hN hK h19 hB hRS hRH hLI (a := a) ha (μ := μ) hμ
end CPS
end
section
open Real Filter Topology MeasureTheory Set Asymptotics
namespace CPS
/-- `σ_a² = Σ_{γ>0} 2/|½+a+iγ|²`. -/
noncomputable def sigmaSq (a : ℝ) : ℝ := ∑' γ : zeroOrdinates, 2 / zeroDen a γ ^ 2
/-- **Theorem 4(a), the variance.** Under RH and LI, `σ_a² = Σ_{γ>0} 2/|½+a+iγ|² ∼ log(A/2π)/(2A)` as `a → ∞`, with `A = a + ½`. -/
theorem _root_.CPS.theorem4a_variance (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    sigmaSq ~[atTop] fun a : ℝ => log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2)) := by
  with_unfolding_all exact CpsLean.sigmaSq_isEquivalent hN hRH hLI
end CPS
end
section
open Real Filter Topology MeasureTheory Set ProbabilityTheory Finset
namespace CPS
/-- **Theorem 4(a).** Assume RH and LI. Then `δ_a → ½` as `a → ∞`. -/
theorem _root_.CPS.theorem4_a (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : CPS.VonKochPsi) (hC : AnsCor13a) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI) :
    Tendsto deltaA atTop (𝓝 (1 / 2)) := by
  with_unfolding_all exact CpsLean.theorem4_a hE hN hK hC h19 hB hRS hRH hLI
end CPS
end
section
open Real Filter Topology MeasureTheory Set Asymptotics
namespace CPS
/-- `B_a(x) = ½ ∫_2^{√x} t^{2a}/log t dt`. -/
noncomputable def biasTerm (a x : ℝ) : ℝ := 1 / 2 * ∫ t in (2 : ℝ)..√x, t ^ (2 * a) / log t
/-- **Remark 1, Mertens.** Unconditionally, by Mertens' second theorem, `½ Σ_{p≤√x} 1/p = ½ log log x + O(1)`. -/
theorem _root_.CPS.remark1_mertens (hM : Mertens2) :
    (fun x : ℝ => 1 / 2 * (∑ p ∈ (Finset.range (⌊√x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p) -
      1 / 2 * log (log x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  with_unfolding_all exact CpsLean.half_sum_primes_isBigO hM
/-- **Remark 1** (deterministic term). For `a > −½`, `B_a(x) ∼ x^{a+½}/((2a+1) log x)`; for `x ≥ 4`, `B_{−½}(x) = ½(log log √x − log log 2)`; and `B_{−½}(x) = ½ log log x + O(1)`. -/
theorem _root_.CPS.remark1_deterministic :
    (∀ a : ℝ, -1 / 2 < a →
      (biasTerm a) ~[atTop] fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x)) ∧
    (∀ x : ℝ, 4 ≤ x → biasTerm (-1 / 2) x = 1 / 2 * (log (log √x) - log (log 2))) ∧
    ((fun x : ℝ => biasTerm (-1 / 2) x - 1 / 2 * log (log x)) =O[atTop] (fun _ : ℝ => (1 : ℝ))) := by
  with_unfolding_all exact CpsLean.remark1_deterministic
end CPS
end
section
open Real Filter Topology MeasureTheory Set ProbabilityTheory Asymptotics
namespace CPS
/-- **Theorem 4(b), analytic form, on `deltaA`.** Under RH and LI, with `A = a + ½`, `½ − δ_a ∼ b_a/(σ_a √(2π))` with `b_a = 1/(2a+1)`, and `½ − δ_a ∼ 1/(2 √(π A log(A/2π)))`, as `a → ∞`. -/
theorem _root_.CPS.theorem4_b (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) (hB : BesselDecay) :
    ((fun a : ℝ => 1 / 2 - deltaA a) ~[atTop]
      fun a : ℝ => (1 / (2 * a + 1)) / (√(sigmaSq a) * √(2 * π))) ∧
    ((fun a : ℝ => 1 / 2 - deltaA a) ~[atTop]
      fun a : ℝ => 1 / (2 * √(π * (a + 1 / 2) * log ((a + 1 / 2) / (2 * π))))) := by
  with_unfolding_all exact CpsLean.theorem4_b hN hRH hLI hB
/-- **Theorem 4(b), on the density.** Assume RH and LI. For every `a > −½` the set where the race `θ_a` is ahead of `li(x^{a+1})` has a logarithmic density `δ a`, and `½ − δ a ∼ 1/(2 √(π A log(A/2π)))` as `a → ∞`, with `A = a + ½`. -/
theorem _root_.CPS.theorem4_b_density (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : CPS.VonKochPsi) (hC : AnsCor13a) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI) :
    ∃ δ : ℝ → ℝ,
      (∀ a : ℝ, -1 / 2 < a → HasLogDensity {x : ℝ | li (x ^ (a + 1)) < thetaPow a x} (δ a)) ∧
      ((fun a : ℝ => 1 / 2 - δ a) ~[atTop]
        fun a : ℝ => 1 / (2 * √(π * (a + 1 / 2) * log ((a + 1 / 2) / (2 * π))))) := by
  with_unfolding_all exact CpsLean.theorem4_b_density hE hN hK hC h19 hB hRS hRH hLI
end CPS
end
namespace CPS
/-- The rows `(n, lo, hi, N_n)` of Table 1; `lo`, `hi` over `10²⁴`. -/
def table1Rows : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 14134725141734693790457250, 14134725141734693790457253, 4691),
   (2, 21022039638771554992628478, 21022039638771554992628481, 176777),
   (3, 25010857580145688763213789, 25010857580145688763213792, 1409533),
   (4, 30424876125859513210311896, 30424876125859513210311899, 23185159),
   (5, 32935061587739189690662367, 32935061587739189690662370, 84474667),
   (6, 37586178158825671257217762, 37586178158825671257217765, 920765957),
   (7, 40918719012147495187398125, 40918719012147495187398128, 5075610989),
   (8, 43327073280914999519496121, 43327073280914999519496124, 17393031977),
   (9, 48005150881167159727942471, 48005150881167159727942474, 189499828967),
   (10, 49773832477672302181916783, 49773832477672302181916786, 466911439271),
   (11, 52970321477714460644147295, 52970321477714460644147298, 2378827903247),
   (12, 56446247697063394804367758, 56446247697063394804367761, 13946348081951),
   (13, 59347044002602353079653647, 59347044002602353079653650, 60934830657541),
   (14, 60831778524609809844259900, 60831778524609809844259903, 129555248013179),
   (15, 65112544048081606660875053, 65112544048081606660875056, 1138383441262829),
   (16, 67079810529494173714478827, 67079810529494173714478830, 3088372227674287),
   (17, 69546401711173979252926856, 69546401711173979252926859, 10787862040659943),
   (18, 72067157674481907582522106, 72067157674481907582522109, 38708026184211401),
   (19, 75704690699083933168326915, 75704690699083933168326918, 244370311869517289),
   (20, 77144840068874805372682663, 77144840068874805372682666, 506690435563768739)]
/-- The first-crossing primes `N_n` of Table 1 are prime. -/
theorem _root_.CPS.table1_primes : ∀ r ∈ table1Rows, Nat.Prime r.2.2.2 := by
  with_unfolding_all exact CpsLean.table1_primes
end CPS
section
open Real Set
namespace CPS
/-- The values of `S_N` in the paper; `4691` is prime. -/
theorem _root_.CPS.grid_integers :
    S 10 = 18 ∧ S 100 = 1061 ∧ S 1000 = 76128 ∧ S 10000 = 5736397 ∧
      Nat.Prime 4691 ∧ S 4691 = 1378036 := by
  with_unfolding_all exact CpsLean.grid_integers
/-- `Σ_{p≤x} p = S_x − 1` in the table of Section 9.1. -/
theorem _root_.CPS.first_crossing_table :
    S 103 = 1265 ∧ S 107 = 1372 ∧ S 109 = 1481 ∧ S 112 = 1481 ∧ S 113 = 1594 ∧ S 127 = 1721 := by
  with_unfolding_all exact CpsLean.first_crossing_table
/-- **The first crossing at `a = 1`.** On `x ≥ 2`, the least `x` with `li(x²) < θ₁(x)` is `109`. -/
theorem _root_.CPS.first_crossing_a1 :
    IsLeast {x : ℝ | 2 ≤ x ∧ li (x ^ ((1 : ℝ) + 1)) < thetaPow 1 x} 109 := by
  with_unfolding_all exact CpsLean.first_crossing_a1
/-- **Arb certificate of Table 1.** For each row `(n, lo, hi, N)` of `table1Rows`, `m = π(N)`: the `n`-th zero has ordinate `γ ∈ (lo/10²⁴, hi/10²⁴)`, `σ_{m−1} < lo/10²⁴`, `hi/10²⁴ ≤ σ_m`. Two points of trust: the sums `S(N_n)` come from primesum (`02_certify.py`, `run.jsonl` = Zenodo 10.5281/zenodo.23269807), rechecked by sieve for `n ≤ 5`; the index `zeroCount γ = n` comes from Arb's rigorous isolation of the zeros (`acb_dirichlet_zeta_zeros`), 400 bits. Intervals: `scripts/numerics/certify_table1.py`, output `table1_cert.txt`. A numerical certificate, taken as a hypothesis. -/
def Table1Cert : Prop :=
  ∀ r ∈ table1Rows, ∃ γ ∈ zeroOrdinates, zeroCount γ = r.1 ∧
    (r.2.1 : ℝ) / 10 ^ 24 < γ ∧ γ < (r.2.2.1 : ℝ) / 10 ^ 24 ∧
    sigma (Nat.primeCounting r.2.2.2 - 1) < (r.2.1 : ℝ) / 10 ^ 24 ∧
    (r.2.2.1 : ℝ) / 10 ^ 24 ≤ sigma (Nat.primeCounting r.2.2.2)
/-- **Table 1**, with `Table1Cert`: `σ_{m−1} < γ_n ≤ σ_m`, `m = π(N_n)`, and `N(γ_n) = N_n`, `n ≤ 20`. -/
theorem _root_.CPS.table1_crossing (h : Table1Cert) : ∀ r ∈ table1Rows, r.2.2.2.Prime ∧
    ∃ γ ∈ zeroOrdinates, zeroCount γ = r.1 ∧
      (r.2.1 : ℝ) / 10 ^ 24 < γ ∧ γ < (r.2.2.1 : ℝ) / 10 ^ 24 ∧
      sigma (Nat.primeCounting r.2.2.2 - 1) < γ ∧ γ ≤ sigma (Nat.primeCounting r.2.2.2) ∧
      firstCrossing γ = r.2.2.2 := by
  with_unfolding_all exact CpsLean.table1_crossing h
end CPS
end
end
