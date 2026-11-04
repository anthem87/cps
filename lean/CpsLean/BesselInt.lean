module

public import CpsLean.Bessel
public import CpsLean.LimitDist
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Complex.Exponential
set_option autoImplicit false

/-!
# The integral form of `J₀` and its elementary bounds

* `ansJ0_eq`: `∫_0^1 e^{−iz cos(2πt)} dt = J₀(z)`, the power series.
* `abs_besselJ0_le_one`, `besselJ0_neg`: `|J₀(x)| ≤ 1`, `J₀(−x) = J₀(x)`.
* `abs_besselJ0_sub_one_le`: `|J₀(x) − 1| ≤ x²/2`.
* `abs_besselJ0_sub_exp_le`: `|J₀(x) − e^{−x²/4}| ≤ x⁴/8`, for every real `x`.
-/

open Finset Real Filter Topology Nat MeasureTheory

@[expose] public section

namespace CpsLean

/-- `∫_0^{2π} cos^{n+2} = (n+1)/(n+2) ∫_0^{2π} cos^n`. -/
theorem wallis_step (n : ℕ) :
    ∫ x in (0 : ℝ)..(2 * π), cos x ^ (n + 2) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ x in (0 : ℝ)..(2 * π), cos x ^ n := by
  rw [integral_cos_pow]
  simp

/-- `∫_0^{2π} cos^{2k} · 4^k (k!)² = 2π (2k)!`. -/
theorem wallis_even (k : ℕ) :
    (∫ x in (0 : ℝ)..(2 * π), cos x ^ (2 * k)) * (4 ^ k * (k ! : ℝ) ^ 2) =
      2 * π * ((2 * k)! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2, wallis_step (2 * k), factorial_succ k]
    have hf : ((2 * k + 2)! : ℝ) = (2 * (k : ℝ) + 2) * ((2 * (k : ℝ) + 1) * ((2 * k)! : ℝ)) := by
      rw [factorial_succ (2 * k + 1), factorial_succ (2 * k)]
      push_cast
      ring
    rw [hf]
    push_cast
    have hk : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
    set J := ∫ x in (0 : ℝ)..(2 * π), cos x ^ (2 * k) with hJ
    calc (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) * J * (4 ^ (k + 1) * (((k : ℝ) + 1) * (k ! : ℝ)) ^ 2)
        = (2 * (k : ℝ) + 1) * (2 * ((k : ℝ) + 1)) * (J * (4 ^ k * (k ! : ℝ) ^ 2)) := by
          field_simp
          ring
      _ = _ := by
          rw [ih]
          ring

/-- `∫_0^{2π} cos^{2k+1} = 0`. -/
theorem wallis_odd (k : ℕ) : ∫ x in (0 : ℝ)..(2 * π), cos x ^ (2 * k + 1) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [h2, wallis_step (2 * k + 1), ih, mul_zero]

/-- `∫_0^1 cos^n(2πt) dt = (2π)⁻¹ ∫_0^{2π} cos^n`. -/
theorem integral_cos_two_pi_pow (n : ℕ) :
    ∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ n = (2 * π)⁻¹ * ∫ x in (0 : ℝ)..(2 * π), cos x ^ n := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun x => cos x ^ n)
    (show (2 * π) ≠ 0 by positivity)
  simpa using h

/-- **`J₀` in integral form.** `∫_0^1 e^{−iz cos(2πt)} dt = J₀(z)`. -/
theorem ansJ0_eq (z : ℝ) : ansJ0 z = (besselJ0 z : ℂ) := by
  set w : ℝ → ℂ := fun t => -Complex.I * (z : ℂ) * (Real.cos (2 * π * t) : ℂ) with hw
  have hwn : ∀ t, ‖w t‖ ≤ |z| := fun t => by
    simp only [hw, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hsum : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..1, w t ^ n / (n ! : ℂ))
      (∫ t in (0 : ℝ)..1, Complex.exp (w t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => |z| ^ n / (n ! : ℝ)) ?_ ?_ ?_ ?_ ?_
    · intro n
      have hc : Continuous fun t : ℝ => w t ^ n / (n ! : ℂ) := by
        simp only [hw]
        fun_prop
      exact hc.aestronglyMeasurable
    · intro n
      refine ae_of_all _ fun t _ => ?_
      rw [norm_div, norm_pow, Complex.norm_natCast]
      gcongr
      exact hwn t
    · exact ae_of_all _ fun t _ => Real.summable_pow_div_factorial _
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun t _ => ?_
      have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (w t)
      rwa [← Complex.exp_eq_exp_ℂ] at this
  -- the value of the terms
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..1, w t ^ n / (n ! : ℂ) =
      ((-Complex.I * (z : ℂ)) ^ n / (n ! : ℂ)) *
        ((∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ n : ℝ) : ℂ) := by
    intro n
    rw [intervalIntegral.integral_ofReal.symm.trans rfl, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hw]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm] at hsum
  -- odd terms vanish
  have hodd : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      ((-Complex.I * (z : ℂ)) ^ n / (n ! : ℂ)) *
        ((∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ n : ℝ) : ℂ) = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · exact absurd ⟨k, rfl⟩ hn
      · exact ⟨k, rfl⟩
    rw [integral_cos_two_pi_pow, wallis_odd]
    simp
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have heven := (hinj.hasSum_iff hodd).mpr hsum
  -- comparison with the series
  have hser : HasSum (fun k : ℕ => (((-1 : ℝ) ^ k * ((z ^ 2 / 4) ^ k / (k ! : ℝ) ^ 2) : ℝ) : ℂ))
      (besselJ0 z : ℂ) := Complex.hasSum_ofReal.mpr (besselJ0_hasSum z)
  have hval : ∀ k : ℕ, (∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ (2 * k)) =
      ((2 * k)! : ℝ) / (4 ^ k * (k ! : ℝ) ^ 2) := by
    intro k
    rw [integral_cos_two_pi_pow]
    have hW := wallis_even k
    have hk : (0 : ℝ) < 4 ^ k * (k ! : ℝ) ^ 2 := by positivity
    have hpi : (2 * π) ≠ 0 := by positivity
    rw [eq_div_iff hk.ne', mul_assoc, hW, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  have hfun : ((fun n : ℕ => ((-Complex.I * (z : ℂ)) ^ n / (n ! : ℂ)) *
        ((∫ t in (0 : ℝ)..1, cos (2 * π * t) ^ n : ℝ) : ℂ)) ∘ fun k : ℕ => 2 * k) =
      fun k : ℕ => (((-1 : ℝ) ^ k * ((z ^ 2 / 4) ^ k / (k ! : ℝ) ^ 2) : ℝ) : ℂ) := by
    funext k
    simp only [Function.comp_apply]
    rw [hval k]
    have hsq : (-Complex.I * (z : ℂ)) ^ (2 * k) = (-1 : ℂ) ^ k * (z : ℂ) ^ (2 * k) := by
      rw [pow_mul, pow_mul, ← mul_pow]
      congr 1
      rw [mul_pow, neg_sq, Complex.I_sq]
    have hf0 : (((2 * k)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    have hk0 : ((k ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    have h4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hsq]
    push_cast
    rw [div_pow, ← pow_mul]
    field_simp
  rw [hfun] at heven
  exact heven.unique hser

theorem besselJ0_neg (x : ℝ) : besselJ0 (-x) = besselJ0 x := by
  unfold besselJ0
  refine tsum_congr fun k => ?_
  rw [neg_div, pow_mul, pow_mul, neg_sq]

theorem abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 := by
  have h : ‖ansJ0 x‖ ≤ 1 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1)
      (f := fun t : ℝ => Complex.exp (-Complex.I * (x : ℂ) * (Real.cos (2 * π * t) : ℂ)))
      (fun t _ => by
        have e : -Complex.I * (x : ℂ) * (Real.cos (2 * π * t) : ℂ) =
            ((-(x * Real.cos (2 * π * t)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [e, Complex.norm_exp_ofReal_mul_I])
    rw [sub_zero, abs_one, mul_one] at this
    exact this
  rw [ansJ0_eq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- For `|x| ≤ 2`: `1 − x²/4 ≤ J₀(x)` and `e^{−x²/4} ≤ 1 − x²/4 + x⁴/32`. -/
theorem besselJ0_lower {x : ℝ} (hx : |x| ≤ 2) :
    1 - x ^ 2 / 4 ≤ besselJ0 x ∧ exp (-(x ^ 2 / 4)) ≤ 1 - x ^ 2 / 4 + (x ^ 2 / 4) ^ 2 / 2 := by
  set y := x ^ 2 / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    have : x ^ 2 ≤ 4 := by nlinarith [abs_nonneg x, sq_abs x]
    simp only [y]; linarith
  have ha : Antitone (fun k : ℕ => y ^ k / (k ! : ℝ) ^ 2) := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [pow_succ, factorial_succ]; push_cast
    have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast factorial_pos k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hyk : 0 ≤ y ^ k := pow_nonneg hy0 k
    nlinarith [mul_le_mul_of_nonneg_left hy1 hyk, mul_nonneg hyk (sq_nonneg (k ! : ℝ))]
  have hb : Antitone (fun k : ℕ => y ^ k / (k ! : ℝ)) := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [pow_succ, factorial_succ]; push_cast
    have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hk]
    have hyk : 0 ≤ y ^ k := pow_nonneg hy0 k
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith [mul_le_mul_of_nonneg_left hy1 hyk, mul_nonneg hyk hk.le]
  obtain ⟨hJlo, -⟩ := alternating_bounds ha (besselJ0_hasSum x) 1
  obtain ⟨-, hEhi⟩ := alternating_bounds hb (exp_neg_hasSum y) 1
  simp only [show 2 * 1 = 2 by rfl, show 2 * 1 + 1 = 3 by rfl,
    sum_range_succ, sum_range_zero] at hJlo hEhi
  norm_num [factorial] at hJlo hEhi
  constructor
  · linarith
  · linarith

/-- `|J₀(x) − 1| ≤ x²/2`, for every real `x`. -/
theorem abs_besselJ0_sub_one_le (x : ℝ) : |besselJ0 x - 1| ≤ x ^ 2 / 2 := by
  rcases le_or_gt |x| 2 with hx | hx
  · obtain ⟨h1, -⟩ := besselJ0_lower hx
    obtain ⟨-, h2⟩ := lemmaJ hx
    have h3 : exp (-(x ^ 2 / 4)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  · have h0 := abs_besselJ0_le_one x
    have hsq : 4 < x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    have := abs_sub (besselJ0 x) 1
    rw [abs_one] at this
    linarith

/-- `|J₀(x) − e^{−x²/4}| ≤ x⁴/8`, for every real `x`. -/
theorem abs_besselJ0_sub_exp_le (x : ℝ) : |besselJ0 x - exp (-(x ^ 2 / 4))| ≤ x ^ 4 / 8 := by
  rcases le_or_gt |x| 2 with hx | hx
  · obtain ⟨h1, h2⟩ := besselJ0_lower hx
    obtain ⟨-, h3⟩ := lemmaJ hx
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x ^ 2)]
  · have h0 := abs_besselJ0_le_one x
    have h1 : 0 < exp (-(x ^ 2 / 4)) := exp_pos _
    have h2 : exp (-(x ^ 2 / 4)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hsq : 4 < x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
    have h4 : 16 < x ^ 4 := by nlinarith
    have := abs_sub (besselJ0 x) (exp (-(x ^ 2 / 4)))
    rw [abs_of_pos h1] at this
    linarith

end CpsLean
