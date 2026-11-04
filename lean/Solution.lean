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
end CPS
end
section
open Real
namespace CPS
/-- **Truncated explicit formula for `ψ`** (Davenport, Ch. 17, (9)–(10); Strömbergsson, Thm. 13.2): there is an absolute constant `C` such that, for every real `x ≥ 2` and `T ≥ 2`, `|ψ₀(x) − (x − Σ_{|γ|<T} x^ρ/ρ − ζ′(0)/ζ(0) − ½ log(1 − x^{−2}))| ≤ C (x log²(xT)/T + log x · min(1, x/(T⟨x⟩)))`. Domain as in Strömbergsson's statement; the page in Davenport is to be checked on the volume. An explicit hypothesis, never an axiom. -/
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
/-- **Akbary–Ng–Shahabi, Corollary 1.3(a)** (Q. J. Math. 65 (2014), arXiv:1306.1657, Thm. 1.2 and Cor. 1.3(a)): if `φ` has an expansion (1.6)–(1.7) with `r_n ≪ λ_n^{−β}` for some `β > ½` and `Σ_{T<λ_n≤T+1} 1 ≪ log T`, then `φ` has a limiting distribution. Stated for strictly increasing frequencies. An explicit hypothesis, never an axiom. -/
def AnsCor13a : Prop :=
  ∀ (φ : ℝ → ℝ) (c y₀ : ℝ) (lam : ℕ → ℝ) (r : ℕ → ℂ),
    AnsExpansion φ c y₀ lam r → AnsCond13a lam r →
      ∃ μ : MeasureTheory.ProbabilityMeasure ℝ, HasLimitingDistribution φ μ
end CPS
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
end
