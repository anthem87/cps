module

public import CpsLean.ZeroCount
public import CpsLean.LogIntPV
public import CpsLean.RippleRH
public import CpsLean.Classical.TruncatedExplicitFormula
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
set_option autoImplicit false

/-!
# Lemma A, first part: Abel summation and the remainder of the explicit formula

* `piA a x = Π_a(x) = Σ_{p^k ≤ x} p^{ka}/k`, with `Λ(p^k)/log(p^k) = 1/k`.
* `piA_abel`: `Π_a(x) = 2^a + f(x)ψ(x) − f(5/2) log 2 − ∫_{5/2}^x f′ψ`, with `f(t) = t^a/log t`.
* `zeroZ T t = Σ_{|γ|<T} t^ρ/ρ`, `psiRem T t = ψ(t) − t + Σ_{|γ|<T} t^ρ/ρ`.
* `psiRem_le`: `‖ψ(t) − t + Σ_{|γ|<T} t^ρ/ρ‖ ≤ C (t log²(tT)/T + log t + 1)`, for `t ≥ 2`, `T ≥ 2`.
* `log_pow_le_rpow`, `integral_rpow_div_log_pow_le`: bounds for the integrals of `t^{b−1}/log^k t`.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

@[expose] public section

namespace CpsLean

/-- `Π_a(x) = Σ_{p^k ≤ x} p^{ka}/k`, written with `Λ(p^k)/log(p^k) = 1/k`. -/
noncomputable def piA (a x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) ^ a / log n * Λ n

theorem hasDerivAt_fw_of_lt (a : ℝ) {t : ℝ} (ht : 1 < t) : deriv (fw a) t = fw' a t :=
  (hasDerivAt_fw a ht).deriv

theorem continuousOn_fw'_five_half (a : ℝ) {x : ℝ} :
    ContinuousOn (fw' a) (Set.Icc (5 / 2) x) :=
  (continuousOn_fw' a).mono fun t ht => (by linarith [ht.1] : (2 : ℝ) ≤ t)

theorem sum_vonMangoldt (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  exact (Chebyshev.psi_eq_sum_Icc t).symm

theorem psi_five_half : Chebyshev.psi (5 / 2) = log 2 := by
  have h : ⌊(5 / 2 : ℝ)⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [← sum_vonMangoldt, h]
  have : Finset.Icc 0 2 = {0, 1, 2} := by decide
  rw [this]
  simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- **Abel summation for `Π_a`**, from the lower limit `5/2`. -/
theorem piA_abel (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    piA a x = 2 ^ a + fw a x * Chebyshev.psi x - fw a (5 / 2) * log 2 -
      ∫ t in (5 / 2 : ℝ)..x, fw' a t * Chebyshev.psi t := by
  have hderiv : ∀ t ∈ Set.Icc (5 / 2 : ℝ) x, deriv (fw a) t = fw' a t := fun t ht =>
    hasDerivAt_fw_of_lt a (by linarith [ht.1])
  have h := sum_mul_eq_sub_sub_integral_mul (Λ : ℕ → ℝ) (f := fw a) (a := 5 / 2) (b := x)
    (by norm_num) hx (fun t ht => (hasDerivAt_fw a (by linarith [ht.1])).differentiableAt)
    (((continuousOn_fw'_five_half a).integrableOn_compact isCompact_Icc).congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc)
  simp only [sum_vonMangoldt, psi_five_half] at h
  have hf : ⌊(5 / 2 : ℝ)⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have h2x : 2 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  rw [hf] at h
  -- the sum from `0`: the term `n = 2` is `2^a`
  have hsplit : piA a x = 2 ^ a + ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, fw a k * Λ k := by
    unfold piA
    have hIcc : Finset.Icc 0 ⌊x⌋₊ = {0, 1, 2} ∪ Finset.Ioc 2 ⌊x⌋₊ := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Ioc]
      omega
    have hd : Disjoint ({0, 1, 2} : Finset ℕ) (Finset.Ioc 2 ⌊x⌋₊) := by
      rw [Finset.disjoint_left]
      intro n hn hn2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      simp only [Finset.mem_Ioc] at hn2
      omega
    rw [hIcc, Finset.sum_union hd]
    have hl2 : log 2 ≠ 0 := (log_pos (by norm_num)).ne'
    congr 1
    simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    field_simp
  rw [hsplit, h]
  have hI : ∫ t in Set.Ioc (5 / 2 : ℝ) x, deriv (fw a) t * Chebyshev.psi t =
      ∫ t in (5 / 2 : ℝ)..x, fw' a t * Chebyshev.psi t := by
    rw [intervalIntegral.integral_of_le hx]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [hderiv t ⟨ht.1.le, ht.2⟩]
  rw [hI]
  ring

/-- The finite set of the nontrivial zeros with `|γ| < T`. -/
noncomputable def zerosLt (T : ℝ) : Finset ℂ :=
  ((finite_zeros T).subset fun _ h => ⟨h.1, le_of_lt h.2⟩ :
    {ρ : ℂ | ρ ∈ nontrivialZeros ∧ |ρ.im| < T}.Finite).toFinset

theorem mem_zerosLt {T : ℝ} {ρ : ℂ} : ρ ∈ zerosLt T ↔ ρ ∈ nontrivialZeros ∧ |ρ.im| < T := by
  simp [zerosLt]

theorem zeroSumLt_eq (T : ℝ) (f : ℂ → ℂ) :
    zeroSumLt T f = ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * f ρ := by
  unfold zeroSumLt zerosLt
  exact finsum_mem_eq_finite_toFinset_sum _ _

/-- `Z(t) = Σ_{|γ|<T} t^ρ/ρ`. -/
noncomputable def zeroZ (T t : ℝ) : ℂ := zeroSumLt T (fun ρ => (t : ℂ) ^ ρ / ρ)

/-- `G(t) = ψ(t) − t + Σ_{|γ|<T} t^ρ/ρ`. -/
noncomputable def psiRem (T t : ℝ) : ℂ := ((Chebyshev.psi t - t : ℝ) : ℂ) + zeroZ T t

theorem primePowerDist_nonneg (x : ℝ) : 0 ≤ primePowerDist x :=
  Real.iInf_nonneg fun _ => abs_nonneg _

/-- `|ψ(t) − ψ₀(t)| ≤ ½ log t`, for `t ≥ 1`. -/
theorem abs_psi_sub_psi0_le {t : ℝ} (ht : 1 ≤ t) : |Chebyshev.psi t - psi0 t| ≤ log t / 2 := by
  unfold psi0
  split_ifs with h
  · have hn : Λ ⌊t⌋₊ ≤ log (⌊t⌋₊ : ℝ) := ArithmeticFunction.vonMangoldt_le_log
    rw [h] at hn
    have h0 : 0 ≤ Λ ⌊t⌋₊ := ArithmeticFunction.vonMangoldt_nonneg
    have : Chebyshev.psi t - (Chebyshev.psi t - Λ ⌊t⌋₊ / 2) = Λ ⌊t⌋₊ / 2 := by ring
    rw [this, abs_of_nonneg (by positivity)]
    linarith
  · have : Chebyshev.psi t - (Chebyshev.psi t - 0) = 0 := by ring
    rw [this, abs_zero]
    have := log_nonneg ht
    positivity

/-- The remainder of the explicit formula, with the constant terms absorbed. -/
theorem psiRem_le (hE : TruncatedExplicitFormula) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t T : ℝ, 2 ≤ t → 2 ≤ T →
      ‖psiRem T t‖ ≤ C * (t * log (t * T) ^ 2 / T + log t + 1) := by
  obtain ⟨C, hC⟩ := hE
  set c₀ : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hc₀
  refine ⟨|C| + ‖c₀‖ + 3, by positivity, fun t T ht hT => ?_⟩
  have ht0 : 0 < t := by linarith
  have hT0 : 0 < T := by linarith
  have hlogt : 0 < log t := log_pos (by linarith)
  have hd := primePowerDist_nonneg t
  have hmin0 : 0 ≤ min 1 (t / (T * primePowerDist t)) :=
    le_min zero_le_one (by positivity)
  have hmin1 : min 1 (t / (T * primePowerDist t)) ≤ 1 := min_le_left _ _
  have hA : 0 ≤ t * log (t * T) ^ 2 / T := by positivity
  have hb := hC t T ht hT
  -- the logarithm of `1 − t⁻²`
  have hL : |(1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ)| ≤ 1 := by
    have h1 : t ^ (-2 : ℤ) ≤ 1 / 4 := by
      rw [zpow_neg, inv_eq_one_div]
      have : (4 : ℝ) ≤ t ^ (2 : ℤ) := by
        have : (t : ℝ) ^ (2 : ℤ) = t ^ 2 := by norm_cast
        rw [this]
        nlinarith
      exact one_div_le_one_div_of_le (by norm_num) this
    have h0 : 0 < t ^ (-2 : ℤ) := by positivity
    have hl : log (1 - t ^ (-2 : ℤ)) ≤ 0 := log_nonpos (by linarith) (by linarith)
    have hu : -2 ≤ log (1 - t ^ (-2 : ℤ)) := by
      have h3 := one_sub_inv_le_log_of_pos (show 0 < 1 - t ^ (-2 : ℤ) by linarith)
      have h4 : (1 - t ^ (-2 : ℤ))⁻¹ ≤ 4 / 3 := by
        rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    rw [abs_le]
    constructor <;> linarith
  have hψ := abs_psi_sub_psi0_le (show 1 ≤ t by linarith)
  -- decomposition
  have hdec : psiRem T t = (((psi0 t : ℝ) : ℂ) - ((t : ℂ) - zeroZ T t - c₀ -
        ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ))) + ((Chebyshev.psi t - psi0 t : ℝ) : ℂ) - c₀ -
      ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ) := by
    unfold psiRem
    push_cast
    ring
  have hb' : ‖((psi0 t : ℝ) : ℂ) - ((t : ℂ) - zeroZ T t - c₀ -
      ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ))‖ ≤ |C| * (t * log (t * T) ^ 2 / T + log t) := by
    refine hb.trans ?_
    have hX : t * log (t * T) ^ 2 / T + log t * min 1 (t / (T * primePowerDist t)) ≤
        t * log (t * T) ^ 2 / T + log t := by
      have : log t * min 1 (t / (T * primePowerDist t)) ≤ log t * 1 :=
        mul_le_mul_of_nonneg_left hmin1 hlogt.le
      linarith
    have hX0 : 0 ≤ t * log (t * T) ^ 2 / T + log t * min 1 (t / (T * primePowerDist t)) := by
      positivity
    calc C * (t * log (t * T) ^ 2 / T + log t * min 1 (t / (T * primePowerDist t)))
        ≤ |C| * (t * log (t * T) ^ 2 / T + log t * min 1 (t / (T * primePowerDist t))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hX0
      _ ≤ |C| * (t * log (t * T) ^ 2 / T + log t) := by gcongr
  rw [hdec]
  have n1 : ‖((Chebyshev.psi t - psi0 t : ℝ) : ℂ)‖ ≤ log t / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hψ
  have n2 : ‖((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hL
  set X := t * log (t * T) ^ 2 / T + log t with hXdef
  have hXpos : 0 ≤ X := by positivity
  have hX1 : 0 ≤ X + 1 := by positivity
  have htri := norm_sub_le (((psi0 t : ℝ) : ℂ) - ((t : ℂ) - zeroZ T t - c₀ -
        ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ)) + ((Chebyshev.psi t - psi0 t : ℝ) : ℂ) - c₀)
      ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ)
  have htri2 := norm_sub_le (((psi0 t : ℝ) : ℂ) - ((t : ℂ) - zeroZ T t - c₀ -
        ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ)) + ((Chebyshev.psi t - psi0 t : ℝ) : ℂ)) c₀
  have htri3 := norm_add_le (((psi0 t : ℝ) : ℂ) - ((t : ℂ) - zeroZ T t - c₀ -
        ((1 / 2 * log (1 - t ^ (-2 : ℤ)) : ℝ) : ℂ))) ((Chebyshev.psi t - psi0 t : ℝ) : ℂ)
  have hlogtX : log t ≤ X := by
    rw [hXdef]
    linarith
  have hsum : |C| * X + log t / 2 + ‖c₀‖ + 1 ≤ (|C| + ‖c₀‖ + 3) * (X + 1) := by
    have h1 : 0 ≤ |C| := abs_nonneg C
    have h2 : 0 ≤ ‖c₀‖ := norm_nonneg _
    nlinarith [mul_nonneg h1 hXpos, mul_nonneg h2 hXpos]
  linarith

/-- `log^k x ≤ D x^c`, for `x ≥ 1`, `c > 0`. -/
theorem log_pow_le_rpow (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → log x ^ k ≤ D * x ^ c := by
  set ε : ℝ := c / (k + 1) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨(1 / ε) ^ k, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : log x ≤ x ^ ε / ε := log_le_rpow_div hx0.le hε0
  have h0 : 0 ≤ log x := log_nonneg hx
  have h2 : log x ^ k ≤ (x ^ ε / ε) ^ k := pow_le_pow_left₀ h0 h1 k
  have h3 : (x ^ ε / ε) ^ k = (1 / ε) ^ k * (x ^ ε) ^ k := by
    rw [div_eq_mul_one_div, mul_pow, mul_comm]
  have h4 : (x ^ ε) ^ k = x ^ (ε * k) := by
    rw [← rpow_natCast, ← rpow_mul hx0.le]
  have h5 : ε * k ≤ c := by
    rw [hε]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h6 : x ^ (ε * k) ≤ x ^ c := rpow_le_rpow_of_exponent_le hx h5
  rw [h3, h4] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h6 (by positivity))

theorem log_five_half_pos : 0 < log (5 / 2 : ℝ) := log_pos (by norm_num)

/-- `∫_A^B t^{b−1}/log^k t ≤ (1/log^k A) B^b/b`, for `1 < A ≤ B`, `b > 0`. -/
theorem integral_rpow_div_log_pow_mono {b A B : ℝ} (hb : 0 < b) (k : ℕ) (hA : 1 < A) (hAB : A ≤ B) :
    ∫ t in A..B, t ^ (b - 1) / log t ^ k ≤ 1 / log A ^ k * (B ^ b / b) := by
  have hA0 : 0 < A := by linarith
  have hlA : 0 < log A := log_pos hA
  have hint : ∫ t in A..B, t ^ (b - 1) = (B ^ b - A ^ b) / b := by
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.mem_uIcc]
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> linarith⟩)]
    simp
  have hc1 : ContinuousOn (fun t : ℝ => t ^ (b - 1) / log t ^ k) (Set.uIcc A B) := by
    rw [uIcc_of_le hAB]
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    exact ((continuousAt_id.rpow_const (Or.inl ht0.ne')).div
      ((continuousAt_log ht0.ne').pow k) (pow_ne_zero k (log_pos ht1).ne')).continuousWithinAt
  have hc2 : ContinuousOn (fun t : ℝ => 1 / log A ^ k * t ^ (b - 1)) (Set.uIcc A B) := by
    rw [uIcc_of_le hAB]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl ht0.ne'))).continuousWithinAt
  have hle : ∫ t in A..B, t ^ (b - 1) / log t ^ k ≤ ∫ t in A..B, 1 / log A ^ k * t ^ (b - 1) := by
    refine intervalIntegral.integral_mono_on hAB hc1.intervalIntegrable hc2.intervalIntegrable ?_
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hl : log A ≤ log t := log_le_log hA0 ht.1
    rw [div_eq_mul_one_div, mul_comm]
    have : 1 / log t ^ k ≤ 1 / log A ^ k :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hlA.le hl k)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  rw [intervalIntegral.integral_const_mul, hint] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have : 0 ≤ A ^ b := by positivity
  rw [div_le_div_iff_of_pos_right hb]
  linarith

/-- `∫_{5/2}^x t^{b−1}/log^k t ≤ C x^b/log^k x`, for `b > 0` and `x ≥ 3`. -/
theorem integral_rpow_div_log_pow_le {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      ∫ t in (5 / 2 : ℝ)..x, t ^ (b - 1) / log t ^ k ≤ C * (x ^ b / log x ^ k) := by
  obtain ⟨D, hD, hDb⟩ := log_pow_le_rpow k (half_pos hb)
  set v₀ := log (5 / 2 : ℝ) with hv₀
  have hv₀0 : 0 < v₀ := log_five_half_pos
  refine ⟨2 ^ k / b + 1 / v₀ ^ k * (D / b), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hxb : 0 < x ^ b := by positivity
  have hfrac : 0 < x ^ b / log x ^ k := by positivity
  rcases le_or_gt x ((5 / 2 : ℝ) ^ 2) with hsmall | hbig
  · -- `log x ≤ 2 v₀`
    have h1 := integral_rpow_div_log_pow_mono hb k (A := 5 / 2) (B := x) (by norm_num) (by linarith)
    have hl2 : log x ≤ 2 * v₀ := by
      have := log_le_log hx0 hsmall
      rw [log_pow] at this
      simpa using this
    have h2 : 1 / v₀ ^ k ≤ 2 ^ k / log x ^ k := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [one_mul, ← mul_pow]
      exact pow_le_pow_left₀ hlx.le (by linarith) k
    calc ∫ t in (5 / 2 : ℝ)..x, t ^ (b - 1) / log t ^ k ≤ 1 / v₀ ^ k * (x ^ b / b) := h1
      _ ≤ 2 ^ k / log x ^ k * (x ^ b / b) := by gcongr
      _ = 2 ^ k / b * (x ^ b / log x ^ k) := by field_simp
      _ ≤ (2 ^ k / b + 1 / v₀ ^ k * (D / b)) * (x ^ b / log x ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ hfrac.le
          have : 0 ≤ 1 / v₀ ^ k * (D / b) := by positivity
          linarith
  · -- split at `√x`
    have hs : (5 / 2 : ℝ) ≤ √x := by
      apply le_sqrt_of_sq_le
      exact hbig.le
    have hsx : √x ≤ x := by
      have h1 : (1 : ℝ) ≤ √x := by linarith
      nlinarith [sq_sqrt hx0.le]
    have hs1 : 1 < √x := by linarith
    have hcont : ContinuousOn (fun t : ℝ => t ^ (b - 1) / log t ^ k) (Set.Icc (5 / 2) x) := by
      intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      exact ((continuousAt_id.rpow_const (Or.inl ht0.ne')).div
        ((continuousAt_log ht0.ne').pow k) (pow_ne_zero k (log_pos ht1).ne')).continuousWithinAt
    have hi1 : IntervalIntegrable (fun t : ℝ => t ^ (b - 1) / log t ^ k) volume (5 / 2) √x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs]
      exact hcont.mono (Set.Icc_subset_Icc_right hsx)
    have hi2 : IntervalIntegrable (fun t : ℝ => t ^ (b - 1) / log t ^ k) volume √x x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hsx]
      exact hcont.mono (Set.Icc_subset_Icc_left hs)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have h1 := integral_rpow_div_log_pow_mono hb k (A := 5 / 2) (B := √x) (by norm_num) hs
    have h2 := integral_rpow_div_log_pow_mono hb k (A := √x) (B := x) hs1 hsx
    have hlogs : log √x = log x / 2 := log_sqrt hx0.le
    rw [hlogs] at h2
    have h3 : 1 / (log x / 2) ^ k * (x ^ b / b) = 2 ^ k / b * (x ^ b / log x ^ k) := by
      rw [div_pow]
      field_simp
    have hsb : √x ^ b = x ^ (b / 2) := by
      rw [sqrt_eq_rpow, ← rpow_mul hx0.le]
      ring_nf
    have hmain : x ^ (b / 2) ≤ D * (x ^ b / log x ^ k) := by
      have h4 := hDb x (by linarith)
      have h5 : x ^ b = x ^ (b / 2) * x ^ (b / 2) := by
        rw [← rpow_add hx0]
        ring_nf
      rw [h5, mul_div_assoc', le_div_iff₀ (by positivity)]
      have hpos : 0 < x ^ (b / 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 hpos.le]
    rw [h3] at h2
    have h6 : 1 / v₀ ^ k * (√x ^ b / b) ≤ 1 / v₀ ^ k * (D / b) * (x ^ b / log x ^ k) := by
      rw [hsb, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hmain hb.le
    have h1' : ∫ t in (5 / 2 : ℝ)..√x, t ^ (b - 1) / log t ^ k ≤
        1 / v₀ ^ k * (D / b) * (x ^ b / log x ^ k) := h1.trans h6
    have : (2 ^ k / b + 1 / v₀ ^ k * (D / b)) * (x ^ b / log x ^ k) =
        1 / v₀ ^ k * (D / b) * (x ^ b / log x ^ k) + 2 ^ k / b * (x ^ b / log x ^ k) := by ring
    rw [this]
    exact add_le_add h1' h2

end CpsLean
