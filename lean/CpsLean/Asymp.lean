module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# Two asymptotic lemmas on integrals

* `integral_isEquivalent`: if `f ∼ g`, `g ≥ 0` and `∫_a^x g → ∞`, then `∫_a^x f ∼ ∫_a^x g`.
* `integral_id_div_log_isEquivalent`: `∫_2^x t dt / log t ∼ x² / (2 log x)`.
-/

open Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- **Integral of equivalents.** If `f ∼ g` at `+∞`, `g ≥ 0` on `[a, ∞)` and `∫_a^x g → ∞`, then
`∫_a^x f ∼ ∫_a^x g`. -/
theorem integral_isEquivalent {f g : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, a ≤ x → IntervalIntegrable f volume a x)
    (hg : ∀ x, a ≤ x → IntervalIntegrable g volume a x)
    (hg0 : ∀ t, a ≤ t → 0 ≤ g t) (hfg : f ~[atTop] g)
    (hG : Tendsto (fun x => ∫ t in a..x, g t) atTop atTop) :
    (fun x => ∫ t in a..x, f t) ~[atTop] (fun x => ∫ t in a..x, g t) := by
  refine IsLittleO.isEquivalent (isLittleO_iff.2 fun c hc => ?_)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((isLittleO_iff.1 hfg.isLittleO) (half_pos hc))
  set T := max T₀ a with hT
  have haT : a ≤ T := le_max_right _ _
  set K := |∫ t in a..T, (f t - g t)|
  have hK : 0 ≤ K := abs_nonneg _
  have hev : ∀ᶠ x in atTop, 2 * K / c ≤ ∫ t in a..x, g t := hG.eventually_ge_atTop _
  filter_upwards [hev, eventually_ge_atTop T] with x hx hxT
  have haX : a ≤ x := haT.trans hxT
  have hfgi : ∀ y, a ≤ y → IntervalIntegrable (fun t => f t - g t) volume a y :=
    fun y hy => (hf y hy).sub (hg y hy)
  have hTx : IntervalIntegrable (fun t => f t - g t) volume T x :=
    ((hfgi T haT).symm.trans (hfgi x haX))
  have hgTx : IntervalIntegrable g volume T x := (hg T haT).symm.trans (hg x haX)
  have hsplit : ∫ t in a..x, (f t - g t) = (∫ t in a..T, (f t - g t)) + ∫ t in T..x, (f t - g t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hfgi T haT) hTx).symm
  have hbound : |∫ t in T..x, (f t - g t)| ≤ ∫ t in T..x, c / 2 * g t := by
    have := intervalIntegral.norm_integral_le_of_norm_le hxT
      (f := fun t => f t - g t) (g := fun t => c / 2 * g t) ?_ (hgTx.const_mul _)
    · simpa [Real.norm_eq_abs] using this
    refine Filter.Eventually.of_forall fun t ht => ?_
    have htT : T₀ ≤ t := (le_max_left _ _).trans ht.1.le
    have := hT₀ t htT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg0 t (haT.trans ht.1.le))] at this
    simpa [Real.norm_eq_abs] using this
  have hgsplit : ∫ t in a..x, g t = (∫ t in a..T, g t) + ∫ t in T..x, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hg T haT) hgTx).symm
  have hgaT : 0 ≤ ∫ t in a..T, g t :=
    intervalIntegral.integral_nonneg haT fun t ht => hg0 t ht.1
  have hGx : 0 ≤ ∫ t in a..x, g t := intervalIntegral.integral_nonneg haX fun t ht => hg0 t ht.1
  rw [intervalIntegral.integral_const_mul] at hbound
  have hfx : (∫ t in a..x, f t) - ∫ t in a..x, g t = ∫ t in a..x, (f t - g t) :=
    (intervalIntegral.integral_sub (hf x haX) (hg x haX)).symm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hGx, Pi.sub_apply, hfx, hsplit]
  have h2K : 2 * K ≤ c * ∫ t in a..x, g t := by
    rw [div_le_iff₀ hc] at hx; linarith
  calc |(∫ t in a..T, (f t - g t)) + ∫ t in T..x, (f t - g t)|
      ≤ K + |∫ t in T..x, (f t - g t)| := abs_add_le _ _
    _ ≤ K + c / 2 * ∫ t in T..x, g t := by linarith
    _ ≤ c * ∫ t in a..x, g t := by nlinarith

/-- `t / log t` is continuous on `[2, ∞)`. -/
theorem continuousOn_id_div_log : ContinuousOn (fun t : ℝ => t / log t) (Ici 2) := by
  refine continuousOn_id.div (continuousOn_log.mono fun t ht => ?_) fun t ht => ?_
  · have : (2 : ℝ) ≤ t := ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith
  · have : (2 : ℝ) ≤ t := ht; exact (log_pos (by linarith)).ne'

theorem continuousOn_id_div_log_sq : ContinuousOn (fun t : ℝ => t / log t ^ 2) (Ici 2) := by
  refine continuousOn_id.div ((continuousOn_log.mono fun t ht => ?_).pow 2) fun t ht => ?_
  · have : (2 : ℝ) ≤ t := ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith
  · have : (2 : ℝ) ≤ t := ht; exact pow_ne_zero _ (log_pos (by linarith)).ne'

theorem intervalIntegrable_of_Ici {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 2)) {x y : ℝ}
    (hx : 2 ≤ x) (hy : 2 ≤ y) : IntervalIntegrable f volume x y :=
  (hf.mono fun t ht => by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at ht; exact hx.trans ht.1
    · rw [uIcc_of_ge h] at ht; exact hy.trans ht.1).intervalIntegrable

/-- `∫_2^x t dt / log² t ≤ x / log² 2 + 2 x² / log² x` for `x ≥ 4` (split at `√x`). -/
theorem integral_id_div_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    ∫ t in (2 : ℝ)..x, t / log t ^ 2 ≤ x / log 2 ^ 2 + 2 * x ^ 2 / log x ^ 2 := by
  have hs : 2 ≤ √x := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hx
  have hsx : √x ≤ x := by
    have h1 : 1 ≤ √x := by linarith
    calc √x ≤ √x * √x := le_mul_of_one_le_left (by linarith) h1
      _ = x := mul_self_sqrt (by linarith)
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hlx : 0 < log x := log_pos (by linarith)
  have hi : ∀ y z, 2 ≤ y → 2 ≤ z → IntervalIntegrable (fun t : ℝ => t / log t ^ 2) volume y z :=
    fun y z hy hz => intervalIntegrable_of_Ici continuousOn_id_div_log_sq hy hz
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 2 (√x) le_rfl hs)
    (hi (√x) x hs (by linarith))]
  have h1 : ∫ t in (2 : ℝ)..√x, t / log t ^ 2 ≤ ∫ t in (2 : ℝ)..√x, t / log 2 ^ 2 := by
    refine intervalIntegral.integral_mono_on hs (hi 2 (√x) le_rfl hs)
      ((by fun_prop : Continuous fun t : ℝ => t / log 2 ^ 2).intervalIntegrable _ _) fun t ht => ?_
    have ht2 : 2 ≤ t := ht.1
    have : log 2 ^ 2 ≤ log t ^ 2 := pow_le_pow_left₀ hl2.le (log_le_log (by norm_num) ht2) 2
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) this
  have h2 : ∫ t in √x..x, t / log t ^ 2 ≤ ∫ t in √x..x, 4 * t / log x ^ 2 := by
    refine intervalIntegral.integral_mono_on hsx (hi (√x) x hs (by linarith))
      ((by fun_prop : Continuous fun t : ℝ => 4 * t / log x ^ 2).intervalIntegrable _ _)
      fun t ht => ?_
    have htp : 0 < t := by linarith [ht.1]
    have hlt : log x / 2 ≤ log t := by
      have : log (√x) = log x / 2 := by rw [log_sqrt (by linarith)]
      rw [← this]; exact log_le_log (by linarith) ht.1
    have hlt0 : 0 < log t := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_self_le_mul_self (by linarith) hlt]
  have e1 : ∫ t in (2 : ℝ)..√x, t / log 2 ^ 2 = ((√x) ^ 2 - 2 ^ 2) / 2 / log 2 ^ 2 := by
    rw [intervalIntegral.integral_div, integral_id]
  have e2 : ∫ t in √x..x, 4 * t / log x ^ 2 = 4 * ((x ^ 2 - (√x) ^ 2) / 2) / log x ^ 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_id]
  rw [e1] at h1; rw [e2] at h2
  rw [sq_sqrt (by linarith)] at h1 h2
  have : (x - 2 ^ 2) / 2 / log 2 ^ 2 ≤ x / log 2 ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have : 4 * ((x ^ 2 - x) / 2) / log x ^ 2 ≤ 2 * x ^ 2 / log x ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  linarith

/-- The derivative of `F(t) = t² / (2 log t)`: `F′(t) = t / log t − t / (2 log² t)` on `t > 1`. -/
theorem hasDerivAt_sq_div_two_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => s ^ 2 / (2 * log s)) (t / log t - t / (2 * log t ^ 2)) t := by
  have hl : 0 < log t := log_pos ht
  have h := ((hasDerivAt_pow 2 t).div ((hasDerivAt_log (by linarith)).const_mul 2)
    (by positivity))
  convert h using 1
  field_simp
  ring

/-- `x² / (2 log x) → ∞`. -/
theorem tendsto_sq_div_two_log : Tendsto (fun x : ℝ => x ^ 2 / (2 * log x)) atTop atTop := by
  have hFge : ∀ x : ℝ, 1 < x → x / 2 ≤ x ^ 2 / (2 * log x) := by
    intro x hx
    have hl : 0 < log x := log_pos hx
    have hlx : log x ≤ x := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_gt_atTop 1] with x hx using hFge x hx

/-- **`∫_2^x t dt / log t ∼ x² / (2 log x)`.** -/
theorem integral_id_div_log_isEquivalent :
    (fun x => ∫ t in (2 : ℝ)..x, t / log t) ~[atTop] (fun x => x ^ 2 / (2 * log x)) := by
  set F : ℝ → ℝ := fun s => s ^ 2 / (2 * log s)
  -- `∫_2^x t / log t = F x − F 2 + ½ ∫_2^x t / log² t`
  have hrepr : ∀ x, 2 ≤ x → ∫ t in (2 : ℝ)..x, t / log t =
      F x - F 2 + (1 / 2) * ∫ t in (2 : ℝ)..x, t / log t ^ 2 := by
    intro x hx
    have hderiv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt F (t / log t - t / (2 * log t ^ 2)) t := by
      intro t ht; rw [uIcc_of_le hx] at ht; exact hasDerivAt_sq_div_two_log (by linarith [ht.1])
    have hi1 := intervalIntegrable_of_Ici continuousOn_id_div_log (le_refl 2) hx
    have hi2 := intervalIntegrable_of_Ici continuousOn_id_div_log_sq (le_refl 2) hx
    have hi3 : IntervalIntegrable (fun t => t / (2 * log t ^ 2)) volume 2 x :=
      (hi2.const_mul (1 / 2)).congr fun t _ => by simp only [div_eq_mul_inv, mul_inv]; ring
    have hint : IntervalIntegrable (fun t => t / log t - t / (2 * log t ^ 2)) volume 2 x :=
      hi1.sub hi3
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have e : ∫ t in (2 : ℝ)..x, t / (2 * log t ^ 2) = 1 / 2 * ∫ t in (2 : ℝ)..x, t / log t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by simp only [div_eq_mul_inv, mul_inv]; ring
    rw [intervalIntegral.integral_sub hi1 hi3, e] at hftc
    linarith
  -- the remainder is `o(F)`
  have hFtop : Tendsto F atTop atTop := tendsto_sq_div_two_log
  have hlogx : Tendsto (fun x : ℝ => 2 / log x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp tendsto_log_atTop).const_mul 2
  have hlogdiv : Tendsto (fun x : ℝ => 2 * log x / x) atTop (𝓝 0) := by
    have := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
    simpa [mul_div_assoc] using this
  -- `x² / log² x = F · (2 / log x)` and `x = F · (2 log x / x)`
  have ho1 : (fun x : ℝ => x ^ 2 / log x ^ 2) =o[atTop] F := by
    have h := ((isLittleO_one_iff ℝ).2 hlogx).mul_isBigO (isBigO_refl F atTop)
    simp only [one_mul] at h
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < log x := log_pos hx
    simp only [F]; field_simp
  have ho2 : (fun x : ℝ => x) =o[atTop] F := by
    have h := ((isLittleO_one_iff ℝ).2 hlogdiv).mul_isBigO (isBigO_refl F atTop)
    simp only [one_mul] at h
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < log x := log_pos hx
    have hx0 : 0 < x := by linarith
    simp only [F]; field_simp
  have hoc : (fun _ : ℝ => F 2) =o[atTop] F :=
    isLittleO_const_left.2 (Or.inr (tendsto_abs_atTop_atTop.comp hFtop))
  have hoI : (fun x => ∫ t in (2 : ℝ)..x, t / log t ^ 2) =o[atTop] F := by
    have hb : (fun x => ∫ t in (2 : ℝ)..x, t / log t ^ 2) =O[atTop]
        (fun x : ℝ => x / log 2 ^ 2 + 2 * (x ^ 2 / log x ^ 2)) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 4] with x hx
      have hI0 : 0 ≤ ∫ t in (2 : ℝ)..x, t / log t ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun t ht => by
          have : (0 : ℝ) < t := by linarith [ht.1]
          positivity
      have hle := integral_id_div_log_sq_le hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hI0, one_mul,
        abs_of_nonneg (by positivity)]
      linarith [show 2 * x ^ 2 / log x ^ 2 = 2 * (x ^ 2 / log x ^ 2) by ring]
    exact hb.trans_isLittleO (((ho2.const_mul_left ((log 2 ^ 2)⁻¹)).congr_left (fun x => by ring)).add
      (ho1.const_mul_left 2))
  refine IsLittleO.isEquivalent ?_
  refine ((hoc.neg_left).add (hoI.const_mul_left (1 / 2))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with x hx
  simp only [Pi.sub_apply]
  rw [hrepr x hx]; ring

end CpsLean
