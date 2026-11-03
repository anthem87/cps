module

public import CpsLean.RippleRH
set_option autoImplicit false

/-!
# The prime-square layer: Theorem 3, Step 2

Under von Koch's theorem and the Riemann hypothesis, for every real `b > −1`,
`θ_b(y) = y^{b+1} / ((b+1) log y) · (1 + O(1/log y))` (`thetaPow_isBigO`), and therefore, for every
real `a > −½`, the layer `k = 2` of `Π_a` is

`½ θ_{2a}(√x) = x^{a+1/2} / ((2a+1) log x) · (1 + O(1/log x))` (`step2_bias_layer`),

the boxed formula of Step 2. The error `O(1/log x)` comes from `∫_2^y t^b dt / log t`; the
contribution of `θ(t) − t` is smaller, `O(y^{b+γ})` with `γ = max(3/4, (1−b)/2) < 1`.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- `f =o T` when `f = T · h` eventually with `h → 0`. -/
theorem isLittleO_of_eq_mul {f T h : ℝ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (he : ∀ᶠ y in atTop, f y = T y * h y) : f =o[atTop] T := by
  have := ((isLittleO_one_iff ℝ).2 hh).mul_isBigO (isBigO_refl T atTop)
  simp only [one_mul] at this
  exact this.congr' (by filter_upwards [he] with y hy; rw [hy, mul_comm]) EventuallyEq.rfl

/-- `log² y / y^r → 0` for `r > 0`. -/
theorem tendsto_log_sq_div_rpow {r : ℝ} (hr : 0 < r) :
    Tendsto (fun y : ℝ => log y ^ 2 / y ^ r) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show 0 < r / 2 by positivity)).tendsto_div_nhds_zero
  have := h.pow 2
  rw [zero_pow two_ne_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [div_pow, ← rpow_natCast (y ^ (r / 2)), ← rpow_mul hy.le]; norm_num

/-- The exponent `γ = max(3/4, (1−b)/2)`: `½ < γ < 1` and `b + γ > 0` for `b > −1`. -/
noncomputable def gam (b : ℝ) : ℝ := max (3 / 4) ((1 - b) / 2)

theorem gam_gt (b : ℝ) : 1 / 2 < gam b := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem gam_lt {b : ℝ} (hb : -1 < b) : gam b < 1 := max_lt (by norm_num) (by linarith)

theorem add_gam_pos {b : ℝ} (hb : -1 < b) : 0 < b + gam b := by
  rcases le_total (3 / 4 : ℝ) ((1 - b) / 2) with h | h
  · rw [gam, max_eq_right h]; linarith
  · rw [gam, max_eq_left h]; linarith

/-- Under von Koch's theorem and RH: `|θ(t) − t| ≤ C t^γ` for every `t ≥ 2`, for `½ < γ`. -/
theorem theta_sub_le_rpow (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {γ : ℝ} (hγ : 1 / 2 < γ) :
    ∃ C, 0 ≤ C ∧ ∀ t, 2 ≤ t → |Chebyshev.theta t - t| ≤ C * t ^ γ := by
  have hO : (fun x : ℝ => √x * log x ^ 2) =O[atTop] (fun x : ℝ => x ^ γ) := by
    refine (isLittleO_of_eq_mul (h := fun y => log y ^ 2 / y ^ (γ - 1 / 2))
      (tendsto_log_sq_div_rpow (by linarith)) ?_).isBigO
    filter_upwards [eventually_gt_atTop 0] with y hy
    have : y ^ γ = √y * y ^ (γ - 1 / 2) := by
      rw [sqrt_eq_rpow, ← rpow_add hy]; norm_num
    rw [this]; field_simp
  refine uniform_of_isBigO ((theta_sub_isBigO hK hRH).trans hO) (g₀ := 1) one_pos
    (fun t ht => one_le_rpow (by linarith) (by linarith)) theta_sub_loc

theorem abs_fw'_le (b : ℝ) {t : ℝ} (ht : 2 ≤ t) :
    |fw' b t| ≤ (|b| / log 2 + 1 / log 2 ^ 2) * t ^ (b - 1) := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl : log 2 ≤ log t := log_le_log (by norm_num) ht
  have hlt : 0 < log t := by linarith
  have htp : 0 < t ^ (b - 1) := rpow_pos_of_pos (by linarith) _
  unfold fw'
  rw [abs_mul, abs_of_pos htp, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ htp.le
  calc |b / log t - 1 / log t ^ 2| ≤ |b / log t| + |1 / log t ^ 2| := abs_sub _ _
    _ = |b| / log t + 1 / log t ^ 2 := by
        rw [abs_div, abs_of_pos hlt, abs_of_pos (show (0 : ℝ) < 1 / log t ^ 2 by positivity)]
    _ ≤ |b| / log 2 + 1 / log 2 ^ 2 := by
        gcongr

/-- `|θ_b(y) − ∫_2^y t^b dt / log t| ≤ A y^{b+γ}` for `y ≥ 2`. -/
theorem thetaPow_sub_integral_le (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {b : ℝ} (hb : -1 < b) :
    ∃ A, ∀ y, 2 ≤ y → |thetaPow b y - ∫ t in (2 : ℝ)..y, fw b t| ≤ A * y ^ (b + gam b) := by
  obtain ⟨C, hC0, hC⟩ := theta_sub_le_rpow hK hRH (gam_gt b)
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hbg := add_gam_pos hb
  set K := (|b| / log 2 + 1 / log 2 ^ 2) * C
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * |fw b 2| + C / log 2 + K / (b + gam b), fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hly : log 2 ≤ log y := log_le_log (by norm_num) hy
  have hY : 1 ≤ y ^ (b + gam b) := one_le_rpow (by linarith) hbg.le
  rw [thetaPow_eq b hy]
  have e1 : |fw b y * (Chebyshev.theta y - y)| ≤ C / log 2 * y ^ (b + gam b) := by
    rw [abs_mul, fw, abs_div, abs_of_pos (rpow_pos_of_pos hy0 _), abs_of_pos (by linarith)]
    calc y ^ b / log y * |Chebyshev.theta y - y| ≤ y ^ b / log 2 * (C * y ^ gam b) :=
          mul_le_mul (div_le_div_of_nonneg_left (rpow_pos_of_pos hy0 _).le hl2 hly) (hC y hy)
            (abs_nonneg _) (by positivity)
      _ = C / log 2 * y ^ (b + gam b) := by rw [rpow_add hy0]; ring
  have e2 : |∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t)| ≤ K / (b + gam b) * y ^ (b + gam b) := by
    have hb' : ∀ t ∈ uIoc (2 : ℝ) y, ‖fw' b t * (Chebyshev.theta t - t)‖ ≤ K * t ^ (b - 1 + gam b) := by
      intro t ht
      rw [uIoc_of_le hy] at ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_mul]
      calc |fw' b t| * |Chebyshev.theta t - t| ≤ (|b| / log 2 + 1 / log 2 ^ 2) * t ^ (b - 1) *
            (C * t ^ gam b) := mul_le_mul (abs_fw'_le b ht2) (hC t ht2) (abs_nonneg _) (by positivity)
        _ = K * t ^ (b - 1 + gam b) := by rw [rpow_add ht0]; ring
    have hint : IntervalIntegrable (fun t : ℝ => K * t ^ (b - 1 + gam b)) volume 2 y :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K
    have := intervalIntegral.norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall
      fun t ht => hb' t (by rw [uIoc_of_le hy]; exact ht)) hint
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith))] at this
    rw [show b - 1 + gam b + 1 = b + gam b by ring] at this
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (b + gam b) := by positivity
    calc _ ≤ K * ((y ^ (b + gam b) - 2 ^ (b + gam b)) / (b + gam b)) := this
      _ ≤ K * (y ^ (b + gam b) / (b + gam b)) := by
          gcongr; linarith
      _ = K / (b + gam b) * y ^ (b + gam b) := by ring
  have e3 : |2 * fw b 2| ≤ 2 * |fw b 2| * y ^ (b + gam b) := by
    rw [abs_mul, abs_two]; nlinarith [abs_nonneg (fw b 2)]
  calc |(∫ t in (2 : ℝ)..y, fw b t) + 2 * fw b 2 + fw b y * (Chebyshev.theta y - y) -
        (∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t)) - ∫ t in (2 : ℝ)..y, fw b t|
      = |2 * fw b 2 + fw b y * (Chebyshev.theta y - y) -
          ∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t)| := by ring_nf
    _ ≤ |2 * fw b 2| + |fw b y * (Chebyshev.theta y - y)| +
          |∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t)| := by
        refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ (2 * |fw b 2| + C / log 2 + K / (b + gam b)) * y ^ (b + gam b) := by nlinarith

/-- `G(t) = t^{b+1} / ((b+1) log t)` has derivative `t^b / log t − t^b / ((b+1) log² t)`. -/
theorem hasDerivAt_G {b : ℝ} (hb : -1 < b) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => s ^ (b + 1) / ((b + 1) * log s))
      (fw b t - t ^ b / ((b + 1) * log t ^ 2)) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht
  have hb1 : b + 1 ≠ 0 := by linarith
  have h := (hasDerivAt_rpow_const (p := b + 1) (Or.inl ht0.ne')).div
    ((hasDerivAt_log ht0.ne').const_mul (b + 1)) (mul_ne_zero hb1 hl.ne')
  convert h using 1
  rw [add_sub_cancel_right, fw, rpow_add_one ht0.ne']
  field_simp

/-- `∫_2^y t^b dt / log² t ≤ y^{(b+1)/2} / ((b+1) log² 2) + 4 y^{b+1} / ((b+1) log² y)`, `y ≥ 4`. -/
theorem integral_rpow_div_log_sq_le {b : ℝ} (hb : -1 < b) {y : ℝ} (hy : 4 ≤ y) :
    ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 ≤
      √y ^ (b + 1) / ((b + 1) * log 2 ^ 2) + 4 * y ^ (b + 1) / ((b + 1) * log y ^ 2) := by
  have hb1 : 0 < b + 1 := by linarith
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hs : 2 ≤ √y := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt hy
  have hsy : √y ≤ y := by
    have : 1 ≤ √y := by linarith
    calc √y ≤ √y * √y := le_mul_of_one_le_left (by linarith) this
      _ = y := mul_self_sqrt (by linarith)
  have hly : 0 < log y := log_pos (by linarith)
  have hcont : ContinuousOn (fun t : ℝ => t ^ b / log t ^ 2) (Ici 2) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
    exact ((continuousAt_id.rpow_const (Or.inl (by simp; linarith))).div
      ((continuousAt_log (by linarith)).pow 2) (pow_ne_zero 2 hl)).continuousWithinAt
  have hi : ∀ u v, 2 ≤ u → 2 ≤ v → IntervalIntegrable (fun t : ℝ => t ^ b / log t ^ 2) volume u v :=
    fun u v hu hv => intervalIntegrable_of_Ici hcont hu hv
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 2 (√y) le_rfl hs)
    (hi (√y) y hs (by linarith))]
  have hrp : ∀ u v : ℝ, 0 < u → IntervalIntegrable (fun t : ℝ => t ^ b) volume u v := fun u v hu =>
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h1 : ∫ t in (2 : ℝ)..√y, t ^ b / log t ^ 2 ≤ ∫ t in (2 : ℝ)..√y, t ^ b / log 2 ^ 2 := by
    refine intervalIntegral.integral_mono_on hs (hi 2 (√y) le_rfl hs)
      ((hrp 2 (√y) (by norm_num)).div_const _) fun t ht => ?_
    have ht2 : 2 ≤ t := ht.1
    exact div_le_div_of_nonneg_left (rpow_pos_of_pos (by linarith) _).le (by positivity)
      (pow_le_pow_left₀ hl2.le (log_le_log (by norm_num) ht2) 2)
  have h2 : ∫ t in √y..y, t ^ b / log t ^ 2 ≤ ∫ t in √y..y, 4 * t ^ b / log y ^ 2 := by
    refine intervalIntegral.integral_mono_on hsy (hi (√y) y hs (by linarith))
      (((hrp (√y) y (by linarith)).const_mul 4).div_const _) fun t ht => ?_
    have htp : 0 < t := by linarith [ht.1]
    have hlt : log y / 2 ≤ log t := by
      have : log √y = log y / 2 := by rw [log_sqrt (by linarith)]
      rw [← this]; exact log_le_log (by linarith) ht.1
    have hlt0 : 0 < log t := by linarith
    have hpow : 0 < t ^ b := rpow_pos_of_pos htp _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_self_le_mul_self (by linarith) hlt, mul_pos hpow hpow]
  rw [intervalIntegral.integral_div, integral_rpow (Or.inl hb)] at h1
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hb)] at h2
  have h1' : (√y ^ (b + 1) - 2 ^ (b + 1)) / (b + 1) / log 2 ^ 2 ≤
      √y ^ (b + 1) / ((b + 1) * log 2 ^ 2) := by
    rw [div_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (b + 1)]
  have h2' : 4 * ((y ^ (b + 1) - √y ^ (b + 1)) / (b + 1)) / log y ^ 2 ≤
      4 * y ^ (b + 1) / ((b + 1) * log y ^ 2) := by
    rw [mul_div_assoc', div_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < √y ^ (b + 1) := rpow_pos_of_pos (by linarith) _
    have : 0 < y ^ (b + 1) := rpow_pos_of_pos (by linarith) _
    linarith
  linarith

/-- **`θ_b(y) = y^{b+1} / ((b+1) log y) · (1 + O(1/log y))`** under von Koch's theorem and RH. -/
theorem thetaPow_isBigO (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {b : ℝ} (hb : -1 < b) :
    (fun y : ℝ => thetaPow b y - y ^ (b + 1) / ((b + 1) * log y)) =O[atTop]
      (fun y : ℝ => y ^ (b + 1) / log y ^ 2) := by
  obtain ⟨A, hA⟩ := thetaPow_sub_integral_le hK hRH hb
  have hb1 : 0 < b + 1 := by linarith
  set T : ℝ → ℝ := fun y => y ^ (b + 1) / log y ^ 2
  -- `∫_2^y f_b = G(y) − G(2) + (b+1)⁻¹ ∫_2^y t^b / log² t`
  set G : ℝ → ℝ := fun s => s ^ (b + 1) / ((b + 1) * log s)
  have hrepr : ∀ y, 2 ≤ y → (∫ t in (2 : ℝ)..y, fw b t) =
      G y - G 2 + (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by
    intro y hy
    have hcont2 : ContinuousOn (fun t : ℝ => t ^ b / ((b + 1) * log t ^ 2)) (Ici 2) := by
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht
      have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
      exact ((continuousAt_id.rpow_const (Or.inl (by simp; linarith))).div
        (continuousAt_const.mul ((continuousAt_log (by linarith)).pow 2))
        (mul_ne_zero hb1.ne' (pow_ne_zero 2 hl))).continuousWithinAt
    have hi1 := intervalIntegrable_of_Ici (continuousOn_fw b) le_rfl hy
    have hi2 := intervalIntegrable_of_Ici hcont2 le_rfl hy
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_G hb (by rw [uIcc_of_le hy] at ht; linarith [ht.1])) (hi1.sub hi2)
    rw [intervalIntegral.integral_sub hi1 hi2] at hftc
    have : ∫ t in (2 : ℝ)..y, t ^ b / ((b + 1) * log t ^ 2) =
        (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by field_simp
    rw [this] at hftc
    linarith
  -- the three remainders are `o(T)`
  have hT1 : (fun y : ℝ => y ^ (b + gam b)) =o[atTop] T := by
    refine isLittleO_of_eq_mul (h := fun y => log y ^ 2 / y ^ (1 - gam b))
      (tendsto_log_sq_div_rpow (by linarith [gam_lt hb])) ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    have hy0 : 0 < y := by linarith
    have hl : 0 < log y := log_pos hy
    have : y ^ (b + 1) = y ^ (b + gam b) * y ^ (1 - gam b) := by rw [← rpow_add hy0]; ring_nf
    simp only [T]; rw [this]
    have : 0 < y ^ (1 - gam b) := rpow_pos_of_pos hy0 _
    field_simp
  have hTtop : Tendsto T atTop atTop := by
    have h0 : Tendsto (fun y : ℝ => log y ^ 2 / y ^ (b + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_log_sq_div_rpow hb1, by
        filter_upwards [eventually_gt_atTop 1] with y hy
        have : 0 < log y := log_pos hy
        exact div_pos (by positivity) (rpow_pos_of_pos (by linarith) _)⟩
    refine h0.inv_tendsto_nhdsGT_zero.congr' ?_
    filter_upwards with y
    simp only [T, Pi.inv_apply, inv_div]
  have hT2 : (fun _ : ℝ => (1 : ℝ)) =o[atTop] T :=
    isLittleO_const_left.2 (Or.inr (tendsto_abs_atTop_atTop.comp hTtop))
  have hT3 : (fun y : ℝ => √y ^ (b + 1)) =o[atTop] T := by
    refine isLittleO_of_eq_mul (h := fun y => log y ^ 2 / y ^ ((b + 1) / 2))
      (tendsto_log_sq_div_rpow (by linarith)) ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    have hy0 : 0 < y := by linarith
    have hl : 0 < log y := log_pos hy
    have hs : √y ^ (b + 1) = y ^ ((b + 1) / 2) := by
      rw [sqrt_eq_rpow, ← rpow_mul hy0.le]; ring_nf
    have : y ^ (b + 1) = y ^ ((b + 1) / 2) * y ^ ((b + 1) / 2) := by rw [← rpow_add hy0]; ring_nf
    simp only [T]; rw [hs, this]
    have : 0 < y ^ ((b + 1) / 2) := rpow_pos_of_pos hy0 _
    field_simp
  -- assemble
  have hbound : (fun y : ℝ => thetaPow b y - y ^ (b + 1) / ((b + 1) * log y)) =O[atTop]
      (fun y : ℝ => A * y ^ (b + gam b) + |G 2| * 1 + (b + 1)⁻¹ *
        (1 / ((b + 1) * log 2 ^ 2) * √y ^ (b + 1) + 4 / (b + 1) * T y)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 4] with y hy
    have hy2 : 2 ≤ y := by linarith
    have hly : 0 < log y := log_pos (by linarith)
    have hI0 : 0 ≤ ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 :=
      intervalIntegral.integral_nonneg hy2 fun t ht => by
        have : 0 < t := by linarith [ht.1]
        positivity
    have hIle := integral_rpow_div_log_sq_le hb hy
    have hAy := hA y hy2
    have hpos : 0 ≤ A * y ^ (b + gam b) := (abs_nonneg _).trans hAy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    have hR : 0 ≤ A * y ^ (b + gam b) + |G 2| * 1 + (b + 1)⁻¹ *
        (1 / ((b + 1) * log 2 ^ 2) * √y ^ (b + 1) + 4 / (b + 1) * T y) := by
      have : 0 ≤ √y ^ (b + 1) := by positivity
      have : 0 ≤ T y := by simp only [T]; positivity
      positivity
    rw [abs_of_nonneg hR]
    have hsplit : thetaPow b y - y ^ (b + 1) / ((b + 1) * log y) =
        (thetaPow b y - ∫ t in (2 : ℝ)..y, fw b t) - G 2 +
          (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by
      rw [hrepr y hy2]; simp only [G]; ring
    rw [hsplit]
    have hIle' : (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 ≤ (b + 1)⁻¹ *
        (1 / ((b + 1) * log 2 ^ 2) * √y ^ (b + 1) + 4 / (b + 1) * T y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [T]
      calc _ ≤ _ := hIle
        _ = _ := by field_simp
    have : 0 ≤ (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by positivity
    calc |(thetaPow b y - ∫ t in (2 : ℝ)..y, fw b t) - G 2 +
          (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2|
        ≤ |thetaPow b y - ∫ t in (2 : ℝ)..y, fw b t| + |G 2| +
          |(b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2| := by
          refine (abs_add_le _ _).trans ?_; gcongr; exact abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg this]; linarith
  refine hbound.trans ?_
  exact ((hT1.isBigO.const_mul_left A).add (hT2.isBigO.const_mul_left _)).add
    (((hT3.isBigO.const_mul_left _).add ((isBigO_refl T atTop).const_mul_left _)).const_mul_left _)

/-- **Theorem 3, Step 2** (the layer `k = 2`, source of the bias). Under von Koch's theorem and the
Riemann hypothesis, for every real `a > −½`,
`½ θ_{2a}(√x) = x^{a+1/2} / ((2a+1) log x) · (1 + O(1/log x))`. -/
theorem step2_bias_layer (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    (fun x : ℝ => (1 / 2) * thetaPow (2 * a) (√x) - x ^ (a + 1 / 2) / ((2 * a + 1) * log x))
      =O[atTop] (fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x) / log x) := by
  have hb : -1 < 2 * a := by linarith
  have ha1 : 0 < 2 * a + 1 := by linarith
  have h := (thetaPow_isBigO hK hRH hb).comp_tendsto tendsto_sqrt_atTop
  have hpow : ∀ x : ℝ, 0 ≤ x → √x ^ (2 * a + 1) = x ^ (a + 1 / 2) := fun x hx => by
    rw [sqrt_eq_rpow, ← rpow_mul hx]; ring_nf
  have hlog : ∀ x : ℝ, 0 < x → log √x = log x / 2 := fun x hx => log_sqrt hx.le
  have h1 := h.const_mul_left (1 / 2)
  refine (h1.congr' ?_ EventuallyEq.rfl).trans ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < log x := log_pos hx
    simp only [Function.comp_apply]
    rw [hpow x hx0.le, hlog x hx0]
    field_simp
  · refine IsBigO.of_bound (4 * (2 * a + 1)) ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < log x := log_pos hx
    simp only [Function.comp_apply]
    rw [hpow x hx0.le, hlog x hx0]
    have hp : 0 < x ^ (a + 1 / 2) := rpow_pos_of_pos hx0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) <
      x ^ (a + 1 / 2) / (log x / 2) ^ 2), abs_of_pos (by positivity : (0 : ℝ) <
      x ^ (a + 1 / 2) / ((2 * a + 1) * log x) / log x)]
    apply le_of_eq
    have ha1' : a * 2 + 1 ≠ 0 := by linarith
    field_simp
    norm_num

end CpsLean
