module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit false

/-!
# The logarithmic integral `li`, as a principal value

* `li y = PV ∫_0^y du / log u`, for `y > 1`.
* `tendsto_li`: the principal value exists.
* `hasDerivAt_li`: `li′(y) = 1 / log y`, for `y > 1`.
* `integral_rpow_div_log_eq`: `∫_c^x t^a / log t dt = li(x^{a+1}) − li(c^{a+1})` for `a > −1`,
  `1 < c ≤ x`: the substitution `u = t^{a+1}` of the paper.

The principal value comes from `1 / log u = h(u) + 1 / (u − 1)`, with `0 ≤ h ≤ 1` on `(0, ∞)`:
the two sides of the singular part `1 / (u − 1)` cancel.
-/

open Real Filter Topology MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- `li(y) = PV ∫_0^y du / log u = lim_{ε→0⁺} (∫_0^{1−ε} + ∫_{1+ε}^y) du / log u`, for `y > 1`. -/
noncomputable def li (y : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => (∫ u in (0 : ℝ)..(1 - ε), 1 / log u) +
    ∫ u in (1 + ε)..y, 1 / log u)

/-- The regular part `h(u) = 1 / log u − 1 / (u − 1)`. -/
noncomputable def liReg (u : ℝ) : ℝ := 1 / log u - 1 / (u - 1)

theorem liReg_add (u : ℝ) : 1 / log u = liReg u + 1 / (u - 1) := by
  unfold liReg; ring

theorem liReg_bounds {u : ℝ} (hu : 0 < u) : 0 ≤ liReg u ∧ liReg u ≤ 1 := by
  rcases eq_or_ne u 1 with rfl | h1
  · simp [liReg]
  have hl1 : log u ≤ u - 1 := log_le_sub_one_of_pos hu
  have hl2 : (u - 1) / u ≤ log u := by
    have := one_sub_inv_le_log_of_pos hu
    have h : (u - 1) / u = 1 - u⁻¹ := by field_simp
    rwa [h]
  rcases lt_or_gt_of_ne h1 with h | h
  · have hd : u - 1 < 0 := by linarith
    have hl : log u < 0 := log_neg hu h
    have hdu : (u - 1) / u < 0 := div_neg_of_neg_of_pos hd hu
    unfold liReg
    constructor
    · rw [sub_nonneg]
      exact (one_div_le_one_div_of_neg hd hl).mpr hl1
    · have h3 : 1 / (log u) ≤ 1 / ((u - 1) / u) := (one_div_le_one_div_of_neg hl hdu).mpr hl2
      have h4 : 1 / ((u - 1) / u) = u / (u - 1) := by field_simp
      have h5 : u / (u - 1) - 1 / (u - 1) = 1 := by
        field_simp [hd.ne]
      rw [h4] at h3
      linarith
  · have hd : 0 < u - 1 := by linarith
    have hl : 0 < log u := log_pos h
    have hdu : 0 < (u - 1) / u := by positivity
    unfold liReg
    constructor
    · rw [sub_nonneg]
      exact one_div_le_one_div_of_le hl hl1
    · have h3 : 1 / log u ≤ 1 / ((u - 1) / u) := one_div_le_one_div_of_le hdu hl2
      have h4 : 1 / ((u - 1) / u) = u / (u - 1) := by field_simp
      have h5 : u / (u - 1) - 1 / (u - 1) = 1 := by
        field_simp [hd.ne']
      rw [h4] at h3
      linarith

theorem measurable_liReg : Measurable liReg := by
  unfold liReg
  exact (measurable_const.div measurable_log).sub
    (measurable_const.div (measurable_id.sub measurable_const))

theorem intervalIntegrable_liReg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable liReg volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) measurable_liReg.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun u hu => ?_)
  have hu0 : 0 < u := by
    have h1 : min a b < u := hu.1
    have h2 : 0 ≤ min a b := le_min ha hb
    linarith
  obtain ⟨h1, h2⟩ := liReg_bounds hu0
  rw [Real.norm_of_nonneg h1]
  exact h2

/-- `∫_0^{1−ε} du/(u − 1) = log ε`. -/
theorem integral_inv_sub_one_left {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∫ u in (0 : ℝ)..(1 - ε), 1 / (u - 1) = log ε := by
  have hle : (0 : ℝ) ≤ 1 - ε := by linarith
  have hd : ∀ u ∈ uIcc (0 : ℝ) (1 - ε), HasDerivAt (fun s => log (1 - s)) (1 / (u - 1)) u := by
    intro u hu
    rw [uIcc_of_le hle] at hu
    have hne : (1 - u) ≠ 0 := by linarith [hu.2]
    have := ((hasDerivAt_id' u).const_sub 1).log hne
    convert this using 1
    have hne' : u - 1 ≠ 0 := by intro h; apply hne; linarith
    field_simp
    ring
  have hc : ContinuousOn (fun u : ℝ => 1 / (u - 1)) (uIcc 0 (1 - ε)) := by
    rw [uIcc_of_le hle]
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    linarith [hu.2]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- `∫_{1+ε}^y du/(u − 1) = log (y − 1) − log ε`. -/
theorem integral_inv_sub_one_right {ε y : ℝ} (h0 : 0 < ε) (h1 : 1 + ε ≤ y) :
    ∫ u in (1 + ε)..y, 1 / (u - 1) = log (y - 1) - log ε := by
  have hd : ∀ u ∈ uIcc (1 + ε) y, HasDerivAt (fun s => log (s - 1)) (1 / (u - 1)) u := by
    intro u hu
    rw [uIcc_of_le h1] at hu
    have hne : (u - 1) ≠ 0 := by linarith [hu.1]
    have := ((hasDerivAt_id' u).sub_const 1).log hne
    convert this using 1
  have hc : ContinuousOn (fun u : ℝ => 1 / (u - 1)) (uIcc (1 + ε) y) := by
    rw [uIcc_of_le h1]
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    linarith [hu.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

/-- **The principal value exists**, for `y > 1`, and equals `∫_0^y h + log (y − 1)`. -/
theorem tendsto_li {y : ℝ} (hy : 1 < y) :
    Tendsto (fun ε : ℝ => (∫ u in (0 : ℝ)..(1 - ε), 1 / log u) + ∫ u in (1 + ε)..y, 1 / log u)
      (𝓝[>] 0) (𝓝 ((∫ u in (0 : ℝ)..y, liReg u) + log (y - 1))) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  -- the primitive of `h` is continuous on `[0, y]`
  have hP : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, liReg u) (uIcc 0 y) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hy0]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hy0).mp
        (intervalIntegrable_liReg le_rfl hy0))
  have hmem : (1 : ℝ) ∈ uIcc 0 y := by
    rw [uIcc_of_le hy0]
    exact ⟨by norm_num, hy.le⟩
  have hP1 : ContinuousWithinAt (fun s => ∫ u in (0 : ℝ)..s, liReg u) (uIcc 0 y) 1 := hP 1 hmem
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (min 1 (y - 1)) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (by linarith))
  have hl : Tendsto (fun ε : ℝ => ∫ u in (0 : ℝ)..(1 - ε), liReg u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..1, liReg u)) := by
    refine hP1.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have : Tendsto (fun ε : ℝ => 1 - ε) (𝓝 0) (𝓝 (1 - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [hin] with ε hε
      rw [uIcc_of_le hy0]
      have h1 := hε.2.trans_le (min_le_left _ _)
      exact ⟨by linarith, by linarith [hε.1]⟩
  have hr : Tendsto (fun ε : ℝ => ∫ u in (0 : ℝ)..(1 + ε), liReg u) (𝓝[>] 0)
      (𝓝 (∫ u in (0 : ℝ)..1, liReg u)) := by
    refine hP1.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 0) (𝓝 (1 + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [hin] with ε hε
      rw [uIcc_of_le hy0]
      have h1 := hε.2.trans_le (min_le_right _ _)
      exact ⟨by linarith [hε.1], by linarith⟩
  have hmain : Tendsto (fun ε : ℝ => (∫ u in (0 : ℝ)..(1 - ε), liReg u) +
      ((∫ u in (0 : ℝ)..y, liReg u) - ∫ u in (0 : ℝ)..(1 + ε), liReg u) + log (y - 1)) (𝓝[>] 0)
      (𝓝 ((∫ u in (0 : ℝ)..y, liReg u) + log (y - 1))) := by
    have := (hl.add (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..y, liReg u) |>.sub hr)).add_const
      (log (y - 1))
    convert this using 2
    ring
  refine hmain.congr' ?_
  filter_upwards [hin] with ε hε
  have h0 := hε.1
  have h1 := hε.2.trans_le (min_le_left _ _)
  have h2 := hε.2.trans_le (min_le_right _ _)
  have hle : (0 : ℝ) ≤ 1 - ε := by linarith
  have hle2 : 1 + ε ≤ y := by linarith
  have hci1 : IntervalIntegrable (fun u : ℝ => 1 / (u - 1)) volume 0 (1 - ε) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    linarith [hu.2]
  have hci2 : IntervalIntegrable (fun u : ℝ => 1 / (u - 1)) volume (1 + ε) y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle2]
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    linarith [hu.1]
  have e1 : ∫ u in (0 : ℝ)..(1 - ε), 1 / log u =
      (∫ u in (0 : ℝ)..(1 - ε), liReg u) + log ε := by
    simp only [liReg_add]
    rw [intervalIntegral.integral_add (intervalIntegrable_liReg le_rfl hle) hci1,
      integral_inv_sub_one_left h0 h1.le]
  have e2 : ∫ u in (1 + ε)..y, 1 / log u =
      (∫ u in (1 + ε)..y, liReg u) + (log (y - 1) - log ε) := by
    simp only [liReg_add]
    rw [intervalIntegral.integral_add (intervalIntegrable_liReg (by linarith) hy0) hci2,
      integral_inv_sub_one_right h0 hle2]
  have e3 : ∫ u in (1 + ε)..y, liReg u =
      (∫ u in (0 : ℝ)..y, liReg u) - ∫ u in (0 : ℝ)..(1 + ε), liReg u := by
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_liReg le_rfl hy0)
      (intervalIntegrable_liReg le_rfl (by linarith))]
  rw [e1, e2, e3]
  ring

theorem li_eq {y : ℝ} (hy : 1 < y) : li y = (∫ u in (0 : ℝ)..y, liReg u) + log (y - 1) :=
  (tendsto_li hy).limUnder_eq

/-- `li′(y) = 1 / log y`, for `y > 1`. -/
theorem hasDerivAt_li {y : ℝ} (hy : 1 < y) : HasDerivAt li (1 / log y) y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hc : ContinuousAt liReg y := by
    unfold liReg
    have h1 : y - 1 ≠ 0 := by linarith
    exact (continuousAt_const.div (continuousAt_log (by linarith)) (log_pos hy).ne').sub
      (continuousAt_const.div (by fun_prop) h1)
  have hd1 : HasDerivAt (fun s => ∫ u in (0 : ℝ)..s, liReg u) (liReg y) y :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_liReg le_rfl hy0)
      (measurable_liReg.stronglyMeasurable.stronglyMeasurableAtFilter) hc
  have hd2 : HasDerivAt (fun s => log (s - 1)) (1 / (y - 1)) y := by
    have hne : y - 1 ≠ 0 := by linarith
    have := ((hasDerivAt_id' y).sub_const 1).log hne
    convert this using 1
  have h := hd1.add hd2
  rw [← liReg_add] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hy] with s hs
  exact li_eq hs

/-- The substitution `u = t^{a+1}`: `∫_c^x t^a / log t dt = li(x^{a+1}) − li(c^{a+1})`, for `a > −1`
and `1 < c ≤ x`. -/
theorem integral_rpow_div_log_eq {a c x : ℝ} (ha : -1 < a) (hc : 1 < c) (hx : c ≤ x) :
    ∫ t in c..x, t ^ a / log t = li (x ^ (a + 1)) - li (c ^ (a + 1)) := by
  have hb : 0 < a + 1 := by linarith
  have hd : ∀ t ∈ uIcc c x, HasDerivAt (fun s => li (s ^ (a + 1))) (t ^ a / log t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have htb : 1 < t ^ (a + 1) := one_lt_rpow ht1 hb
    have h := (hasDerivAt_li htb).comp t (hasDerivAt_rpow_const (p := a + 1) (Or.inl ht0.ne'))
    have hl : log t ≠ 0 := (log_pos ht1).ne'
    have hval : t ^ a / log t = 1 / log (t ^ (a + 1)) * ((a + 1) * t ^ (a + 1 - 1)) := by
      rw [log_rpow ht0, add_sub_cancel_right]
      field_simp
    rw [hval]
    exact h
  have hcont : ContinuousOn (fun t : ℝ => t ^ a / log t) (uIcc c x) := by
    rw [uIcc_of_le hx]
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    exact ((continuousAt_id.rpow_const (Or.inl ht0.ne')).div (continuousAt_log ht0.ne')
      (log_pos ht1).ne').continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable

end CpsLean
