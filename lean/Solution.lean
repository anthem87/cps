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
end
