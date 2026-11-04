module

public import CpsLean.BesselInt
public import CpsLean.Classical.BesselDecay
set_option autoImplicit false

/-!
# `|J₀| < 1` away from the origin

* `besselJ0_eq_integral`: `J₀(x) = ∫_0^1 cos(x cos 2πt) dt`.
* `continuous_besselJ0`, `abs_besselJ0_lt_one`: continuity, and `|J₀(x)| < 1` for `x ≠ 0`.
* `exists_theta`: `sup_{|u| ≥ √2} |J₀(u)| < 1`, with no numerical value; the decay of `J₀` makes the
  supremum a maximum over a compact set.
-/

open Real Filter Topology MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- `J₀(x) = ∫_0^1 cos(x cos 2πt) dt`. -/
theorem besselJ0_eq_integral (x : ℝ) :
    besselJ0 x = ∫ t in (0 : ℝ)..1, cos (x * cos (2 * π * t)) := by
  have hc : Continuous fun t : ℝ =>
      Complex.exp (-Complex.I * (x : ℂ) * (Real.cos (2 * π * t) : ℂ)) := by fun_prop
  have h := Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)
  have e : (∫ t in (0 : ℝ)..1, Complex.exp (-Complex.I * (x : ℂ) * (Real.cos (2 * π * t) : ℂ))) =
      (besselJ0 x : ℂ) := ansJ0_eq x
  rw [e] at h
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have e2 : -Complex.I * (x : ℂ) * (Real.cos (2 * π * t) : ℂ) =
      ((-(x * Real.cos (2 * π * t)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e2, Complex.exp_ofReal_mul_I_re, cos_neg]

theorem continuous_besselJ0 : Continuous besselJ0 := by
  have h : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..1, cos (x * cos (2 * π * t)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by simp only [Function.uncurry_def]; fun_prop) 0 1
  exact h.congr fun x => (besselJ0_eq_integral x).symm

/-- `|J₀(x)| < 1` for `x ≠ 0`. -/
theorem abs_besselJ0_lt_one {x : ℝ} (hx : x ≠ 0) : |besselJ0 x| < 1 := by
  set v := min |x| 1 with hv
  have hv0 : 0 < v := lt_min (abs_pos.mpr hx) one_pos
  have hv1 : v ≤ 1 := min_le_right _ _
  have hvx : v ≤ |x| := min_le_left _ _
  have hpi := Real.two_le_pi
  have hc1 : cos v < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith) hv0
    simpa using this
  have hc2 : -1 < cos v := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hv0.le (le_refl π) (by linarith)
    simpa using this
  -- a point where the integrand equals `cos v`
  have hratio : |v / x| ≤ 1 := by
    rw [abs_div, abs_of_pos hv0]
    exact div_le_one_of_le₀ hvx (abs_nonneg _)
  obtain ⟨hr1, hr2⟩ := abs_le.mp hratio
  set t₀ := arccos (v / x) / (2 * π) with ht₀
  have ht0 : 0 ≤ t₀ := div_nonneg (arccos_nonneg _) (by positivity)
  have ht1 : t₀ ≤ 1 := by
    rw [ht₀, div_le_one (by positivity)]
    have := arccos_le_pi (v / x)
    linarith
  have hval : x * cos (2 * π * t₀) = v := by
    have e : 2 * π * t₀ = arccos (v / x) := by
      rw [ht₀]
      field_simp
    rw [e, cos_arccos hr1 hr2]
    field_simp
  have hcont : Continuous fun t : ℝ => cos (x * cos (2 * π * t)) := by fun_prop
  have hint := hcont.intervalIntegrable (μ := volume) 0 1
  have hle : (0 : ℝ) ≤ 1 := zero_le_one
  have hpos1 : 0 < ∫ t in (0 : ℝ)..1, (1 - cos (x * cos (2 * π * t))) :=
    intervalIntegral.integral_pos one_pos (by fun_prop)
      (fun t _ => by linarith [cos_le_one (x * cos (2 * π * t))])
      ⟨t₀, ⟨ht0, ht1⟩, by rw [hval]; linarith⟩
  have hpos2 : 0 < ∫ t in (0 : ℝ)..1, (1 + cos (x * cos (2 * π * t))) :=
    intervalIntegral.integral_pos one_pos (by fun_prop)
      (fun t _ => by linarith [neg_one_le_cos (x * cos (2 * π * t))])
      ⟨t₀, ⟨ht0, ht1⟩, by rw [hval]; linarith⟩
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint] at hpos1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint] at hpos2
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hpos1 hpos2
  rw [← besselJ0_eq_integral] at hpos1 hpos2
  rw [abs_lt]
  constructor <;> linarith

theorem abs_besselJ0_abs (u : ℝ) : |besselJ0 (|u|)| = |besselJ0 u| := by
  rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, besselJ0_neg]

/-- `sup_{|u| ≥ √2} |J₀(u)| < 1`. -/
theorem exists_theta (hB : BesselDecay) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ u : ℝ, √2 ≤ |u| → |besselJ0 u| ≤ θ := by
  obtain ⟨C, hC⟩ := hB
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs21 : 1 ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  set R : ℝ := max (√2) ((2 * C) ^ 2) with hR
  have hne : (Icc (√2) R).Nonempty := nonempty_Icc.mpr (le_max_left _ _)
  have hcont : ContinuousOn (fun u => |besselJ0 u|) (Icc (√2) R) :=
    (continuous_abs.comp continuous_besselJ0).continuousOn
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  have hu₀0 : u₀ ≠ 0 := by
    have := hu₀.1
    linarith
  have hM := abs_besselJ0_lt_one hu₀0
  refine ⟨max (1 / 2) |besselJ0 u₀|, le_max_of_le_left (by norm_num),
    max_lt (by norm_num) hM, fun u hu => ?_⟩
  rw [← abs_besselJ0_abs u]
  rcases le_or_gt |u| R with h | h
  · exact le_max_of_le_right (hmax ⟨hu, h⟩)
  · refine le_max_of_le_left ?_
    have hu1 : 1 ≤ |u| := hs21.trans hu
    have huu : |(|u|)| = |u| := abs_abs u
    have := hC |u| (by rw [huu]; exact hu1)
    rw [huu] at this
    refine this.trans ?_
    have hsq : (2 * C) ^ 2 ≤ |u| := (le_max_right _ _).trans h.le
    have h2 := Real.abs_le_sqrt hsq
    have hs : 0 < √|u| := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hs]
    have := le_abs_self (2 * C)
    linarith

end CpsLean
