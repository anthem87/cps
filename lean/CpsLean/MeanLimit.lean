module

public import CpsLean.LimitDist
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false

/-!
# The mean of a limiting distribution

`mean_of_limiting`: if `φ` has the limiting distribution `μ`, the means `(1/Y) ∫_0^Y φ` tend to `c`,
and the second moments `(1/Y) ∫_0^Y φ²` stay bounded, then `μ` has a first moment and it is `c`.
This is the step of the proof of Theorem 3(i) that the first moments converge. It needs the
truncations `f_M(t) = max(−M, min(t, M))`, with `|t − f_M(t)| ≤ t²/M`.
-/

open Real Filter Topology MeasureTheory Set BoundedContinuousFunction
open scoped ENNReal

@[expose] public section

namespace CpsLean

/-- The truncation `f_M(t) = max(−M, min(t, M))`. -/
noncomputable def clampF (M t : ℝ) : ℝ := max (-M) (min t M)

theorem continuous_clampF (M : ℝ) : Continuous (clampF M) := by
  unfold clampF
  fun_prop

theorem abs_clampF_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : ‖clampF M t‖ ≤ M := by
  unfold clampF
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem abs_sub_clampF_le {M : ℝ} (hM : 0 < M) (t : ℝ) : |t - clampF M t| ≤ t ^ 2 / M := by
  unfold clampF
  have hq : 0 ≤ t ^ 2 / M := by positivity
  rcases le_total t M with h1 | h1
  · rcases le_total t (-M) with h2 | h2
    · rw [min_eq_left h1, max_eq_left h2]
      rw [abs_of_nonpos (by linarith), le_div_iff₀ hM]
      nlinarith
    · rw [min_eq_left h1, max_eq_right h2, sub_self, abs_zero]
      exact hq
  · rw [min_eq_right h1, max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith), le_div_iff₀ hM]
    nlinarith

/-- `f_M`, as a bounded continuous function. -/
noncomputable def clampB {M : ℝ} (hM : 0 ≤ M) : BoundedContinuousFunction ℝ ℝ :=
  ofNormedAddCommGroup (clampF M) (continuous_clampF M) M (abs_clampF_le hM)

/-- `g_M(t) = min(t², M)`, as a bounded continuous function. -/
noncomputable def capB {M : ℝ} (hM : 0 ≤ M) : BoundedContinuousFunction ℝ ℝ :=
  ofNormedAddCommGroup (fun t => min (t ^ 2) M) (by fun_prop) M (fun t => by
    rw [Real.norm_of_nonneg (le_min (by positivity) hM)]
    exact min_le_right _ _)

theorem intervalIntegrable_comp_bcf {φ : ℝ → ℝ} (hφ : Measurable φ)
    (f : BoundedContinuousFunction ℝ ℝ) (a b : ℝ) :
    IntervalIntegrable (fun y => f (φ y)) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := ‖f‖) (by simp)
    ((f.continuous.measurable.comp hφ).aestronglyMeasurable) ?_
  exact ae_of_all _ fun y => f.norm_coe_le_norm _

/-- **The mean of a limiting distribution.** -/
theorem mean_of_limiting {φ : ℝ → ℝ} {μ : ProbabilityMeasure ℝ} {c B : ℝ} (hφ : Measurable φ)
    (hloc : ∀ Y : ℝ, IntegrableOn (fun y => φ y ^ 2) (Set.Icc 0 Y)) (hL : HasLimitingDistribution φ μ)
    (hm : Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, φ y) atTop (𝓝 c))
    (hB : ∀ᶠ Y : ℝ in atTop, (1 / Y) * ∫ y in (0 : ℝ)..Y, φ y ^ 2 ≤ B) :
    Integrable (fun t : ℝ => t) (μ : Measure ℝ) ∧ ∫ t, t ∂(μ : Measure ℝ) = c := by
  set ν : Measure ℝ := (μ : Measure ℝ) with hν
  have hsq : ∀ Y : ℝ, 0 ≤ Y → IntervalIntegrable (fun y => φ y ^ 2) volume 0 Y := fun Y hY =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr (hloc Y)
  have hsqint : ∀ Y : ℝ, 0 ≤ Y → 0 ≤ ∫ y in (0 : ℝ)..Y, φ y ^ 2 := fun Y hY =>
    intervalIntegral.integral_nonneg hY fun y _ => by positivity
  have hB0 : 0 ≤ B := by
    obtain ⟨Y, h1, h2⟩ := (hB.and (eventually_gt_atTop (0 : ℝ))).exists
    have := hsqint Y h2.le
    have h3 : 0 ≤ (1 / Y) * ∫ y in (0 : ℝ)..Y, φ y ^ 2 := by positivity
    linarith
  -- Step 1: `∫ min(t², M) dμ ≤ B`
  have hcap : ∀ M : ℝ, ∀ hM : 0 ≤ M, ∫ t, capB hM t ∂ν ≤ B := by
    intro M hM
    refine le_of_tendsto (hL (capB hM)) ?_
    filter_upwards [hB, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
    refine le_trans ?_ hY
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.integral_mono_on hY0.le (intervalIntegrable_comp_bcf hφ _ _ _)
      (hsq Y hY0.le) fun y _ => ?_
    exact min_le_left _ _
  -- Step 2: `t²` is integrable and `∫ t² dμ ≤ B`
  have hlint : ∫⁻ t, ENNReal.ofReal (t ^ 2) ∂ν ≤ ENNReal.ofReal B := by
    set F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (min (t ^ 2) (n : ℝ)) with hF
    have hFm : ∀ n, Measurable (F n) := fun n => by
      simp only [hF]
      fun_prop
    have hFmono : Monotone F := by
      intro n k hnk t
      simp only [hF]
      exact ENNReal.ofReal_le_ofReal
        (min_le_min le_rfl (by exact_mod_cast hnk))
    have hsup : ∀ t : ℝ, ⨆ n, F n t = ENNReal.ofReal (t ^ 2) := by
      intro t
      refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
      refine le_iSup_of_le ⌈t ^ 2⌉₊ ?_
      simp only [hF]
      exact ENNReal.ofReal_le_ofReal (le_min le_rfl (Nat.le_ceil _))
    have hl := lintegral_iSup (μ := ν) hFm hFmono
    simp only [hsup] at hl
    rw [hl]
    refine iSup_le fun n => ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hint := (capB hn).integrable ν
    have hnn : 0 ≤ᵐ[ν] fun t => capB hn t := ae_of_all _ fun t =>
      le_min (by positivity) hn
    have := ofReal_integral_eq_lintegral_ofReal hint hnn
    have hFe : ∫⁻ t, F n t ∂ν = ENNReal.ofReal (∫ t, capB hn t ∂ν) := by
      rw [this]
      rfl
    rw [hFe]
    exact ENNReal.ofReal_le_ofReal (hcap n hn)
  have hsqμ : Integrable (fun t : ℝ => t ^ 2) ν := by
    refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => by positivity)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  have hsqB : ∫ t, t ^ 2 ∂ν ≤ B := by
    have hae : AEStronglyMeasurable (fun t : ℝ => t ^ 2) ν :=
      (measurable_id.pow_const 2).aestronglyMeasurable
    have hnn : 0 ≤ᵐ[ν] fun t : ℝ => t ^ 2 := ae_of_all _ fun t => by positivity
    rw [integral_eq_lintegral_of_nonneg_ae hnn hae]
    exact ENNReal.toReal_le_of_le_ofReal hB0 hlint
  -- Step 3: `t` is integrable
  have hid : Integrable (fun t : ℝ => t) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsqμ) measurable_id.aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  refine ⟨hid, ?_⟩
  -- Step 4: the two errors of the truncation
  have hkey : ∀ M : ℝ, 0 < M → |c - ∫ t, t ∂ν| ≤ 2 * B / M := by
    intro M hM
    set f := clampB hM.le with hf
    have hfv : ∀ t, f t = clampF M t := fun _ => rfl
    have h1 : |(∫ t, f t ∂ν) - ∫ t, t ∂ν| ≤ B / M := by
      rw [← integral_sub (f.integrable ν) hid]
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (hsqμ.div_const M) (ae_of_all _ fun t => ?_)).trans ?_
      · rw [Real.norm_eq_abs, abs_sub_comm, hfv]
        exact abs_sub_clampF_le hM t
      · rw [integral_div]
        exact div_le_div_of_nonneg_right hsqB hM.le
    have h2 : |c - ∫ t, f t ∂ν| ≤ B / M := by
      refine le_of_tendsto (hm.sub (hL f)).abs ?_
      filter_upwards [hB, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
      have hY' : (0 : ℝ) ≤ Y := hY0.le
      have hint : IntervalIntegrable (fun y => φ y) volume 0 Y := by
        have hd := (intervalIntegrable_const (c := (1 : ℝ))).add (hsq Y hY')
        refine hd.mono_fun' hφ.aestronglyMeasurable (ae_of_all _ fun y => ?_)
        change ‖φ y‖ ≤ 1 + φ y ^ 2
        rw [Real.norm_eq_abs]
        nlinarith [sq_abs (φ y), sq_nonneg (|φ y| - 1)]
      have hdiff : (1 / Y) * (∫ y in (0 : ℝ)..Y, φ y) - (1 / Y) * ∫ y in (0 : ℝ)..Y, f (φ y) =
          (1 / Y) * ∫ y in (0 : ℝ)..Y, (φ y - f (φ y)) := by
        rw [intervalIntegral.integral_sub hint (intervalIntegrable_comp_bcf hφ f _ _)]
        ring
      rw [hdiff, abs_mul, abs_of_pos (show 0 < 1 / Y by positivity)]
      have hn : ‖∫ y in (0 : ℝ)..Y, (φ y - f (φ y))‖ ≤ ∫ y in (0 : ℝ)..Y, φ y ^ 2 / M :=
        intervalIntegral.norm_integral_le_of_norm_le hY'
          (ae_of_all _ fun y _ => by
            rw [Real.norm_eq_abs, hfv]
            exact abs_sub_clampF_le hM (φ y))
          ((hsq Y hY').div_const M)
      rw [Real.norm_eq_abs, intervalIntegral.integral_div] at hn
      calc 1 / Y * |∫ y in (0 : ℝ)..Y, (φ y - f (φ y))|
          ≤ 1 / Y * ((∫ y in (0 : ℝ)..Y, φ y ^ 2) / M) :=
            mul_le_mul_of_nonneg_left hn (by positivity)
        _ = ((1 / Y) * ∫ y in (0 : ℝ)..Y, φ y ^ 2) / M := by ring
        _ ≤ B / M := div_le_div_of_nonneg_right hY hM.le
    have htri := abs_sub_le c (∫ t, f t ∂ν) (∫ t, t ∂ν)
    have : 2 * B / M = B / M + B / M := by ring
    linarith
  -- conclusion
  by_contra hne
  have hd : 0 < |c - ∫ t, t ∂ν| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hM : 0 < 4 * (B + 1) / |c - ∫ t, t ∂ν| := by positivity
  have := hkey _ hM
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

end CpsLean
