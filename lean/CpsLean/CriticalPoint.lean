module

public import CpsLean.BiasLayer
public import CpsLean.Classical.Mertens
set_option autoImplicit false

/-!
# Remark 1: the deterministic term and the critical point `a = −½`

`biasTerm a x = B_a(x) = ½ ∫_2^{√x} t^{2a}/log t dt`.

* For `a > −½`: `B_a(x) ∼ x^{a+½}/((2a+1) log x)`.
* `B_{−½}(x) = ½(log log √x − log log 2) = ½ log log x + O(1)`.
* By Mertens: `½ Σ_{p≤√x} 1/p = ½ log log x + O(1)`.
-/

open Real Filter Topology MeasureTheory Set Asymptotics

@[expose] public section

namespace CpsLean

/-- `B_a(x) = ½ ∫_2^{√x} t^{2a}/log t dt`. -/
noncomputable def biasTerm (a x : ℝ) : ℝ := 1 / 2 * ∫ t in (2 : ℝ)..√x, t ^ (2 * a) / log t

/-- `∫_2^y t^b/log t dt = y^{b+1}/((b+1) log y) (1 + O(1/log y))`, unconditionally. -/
theorem integral_fw_isBigO {b : ℝ} (hb : -1 < b) :
    (fun y : ℝ => (∫ t in (2 : ℝ)..y, fw b t) - y ^ (b + 1) / ((b + 1) * log y)) =O[atTop]
      (fun y : ℝ => y ^ (b + 1) / log y ^ 2) := by
  have hb1 : 0 < b + 1 := by linarith
  set T : ℝ → ℝ := fun y => y ^ (b + 1) / log y ^ 2
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
  have hbound : (fun y : ℝ => (∫ t in (2 : ℝ)..y, fw b t) - y ^ (b + 1) / ((b + 1) * log y)) =O[atTop]
      (fun y : ℝ => |G 2| * 1 + (b + 1)⁻¹ *
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
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
    have hR : 0 ≤ |G 2| * 1 + (b + 1)⁻¹ *
        (1 / ((b + 1) * log 2 ^ 2) * √y ^ (b + 1) + 4 / (b + 1) * T y) := by
      have : 0 ≤ √y ^ (b + 1) := by positivity
      have : 0 ≤ T y := by simp only [T]; positivity
      positivity
    rw [abs_of_nonneg hR, hrepr y hy2]
    have hIle' : (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 ≤ (b + 1)⁻¹ *
        (1 / ((b + 1) * log 2 ^ 2) * √y ^ (b + 1) + 4 / (b + 1) * T y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simp only [T]
      calc _ ≤ _ := hIle
        _ = _ := by field_simp
    have hpos : 0 ≤ (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by positivity
    have e : G y - G 2 + (b + 1)⁻¹ * (∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2) -
        y ^ (b + 1) / ((b + 1) * log y) =
        -G 2 + (b + 1)⁻¹ * ∫ t in (2 : ℝ)..y, t ^ b / log t ^ 2 := by
      simp only [G]
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hpos, mul_one]
    linarith
  refine hbound.trans ?_
  exact (hT2.isBigO.const_mul_left _).add
    (((hT3.isBigO.const_mul_left _).add ((isBigO_refl T atTop).const_mul_left _)).const_mul_left _)

/-- **Remark 1, the case `a > −½`.** `B_a(x) ∼ x^{a+½}/((2a+1) log x)`. -/
theorem biasTerm_isEquivalent {a : ℝ} (ha : -1 / 2 < a) :
    (biasTerm a) ~[atTop] fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x) := by
  have hb : -1 < 2 * a := by linarith
  have ha1 : 0 < 2 * a + 1 := by linarith
  have h := (integral_fw_isBigO hb).comp_tendsto tendsto_sqrt_atTop
  have hpow : ∀ x : ℝ, 0 ≤ x → √x ^ (2 * a + 1) = x ^ (a + 1 / 2) := fun x hx => by
    rw [sqrt_eq_rpow, ← rpow_mul hx]; ring_nf
  have hlog : ∀ x : ℝ, 0 < x → log √x = log x / 2 := fun x hx => log_sqrt hx.le
  unfold IsEquivalent
  have h1 : (biasTerm a - fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x)) =O[atTop]
      fun x : ℝ => x ^ (a + 1 / 2) / log x ^ 2 := by
    have h2 := h.const_mul_left (1 / 2)
    refine (h2.congr' ?_ EventuallyEq.rfl).trans ?_
    · filter_upwards [eventually_gt_atTop 1] with x hx
      have hx0 : 0 < x := by linarith
      have hl : 0 < log x := log_pos hx
      simp only [Function.comp_apply, Pi.sub_apply, biasTerm]
      rw [hpow x hx0.le, hlog x hx0]
      unfold fw
      field_simp
    · refine IsBigO.of_bound 4 ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hx0 : 0 < x := by linarith
      have hl : 0 < log x := log_pos hx
      simp only [Function.comp_apply]
      rw [hpow x hx0.le, hlog x hx0]
      have hp : 0 < x ^ (a + 1 / 2) := rpow_pos_of_pos hx0 _
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      field_simp
      norm_num
  refine h1.trans_isLittleO ?_
  refine IsLittleO.of_bound fun c hc => ?_
  filter_upwards [eventually_gt_atTop 1, tendsto_log_atTop.eventually_ge_atTop ((2 * a + 1) / c)]
    with x hx hL
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos hx
  have hp : 0 < x ^ (a + 1 / 2) := rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  rw [div_le_iff₀ hc] at hL
  have e : c * (x ^ (a + 1 / 2) / ((2 * a + 1) * log x)) =
      (c * log x / (2 * a + 1)) * (x ^ (a + 1 / 2) / log x ^ 2) := by
    field_simp
  rw [e]
  refine le_mul_of_one_le_left (by positivity) ?_
  rw [one_le_div ha1]
  linarith

/-- **Remark 1, the critical point.** `B_{−½}(x) = ½(log log √x − log log 2)`, for `x ≥ 4`. -/
theorem biasTerm_critical {x : ℝ} (hx : 4 ≤ x) :
    biasTerm (-1 / 2) x = 1 / 2 * (log (log √x) - log (log 2)) := by
  have hs : 2 ≤ √x := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  unfold biasTerm
  congr 1
  have hd : ∀ t ∈ uIcc 2 √x, HasDerivAt (fun s : ℝ => log (log s)) (t ^ (2 * (-1 / 2 : ℝ)) / log t) t := by
    intro t ht
    rw [uIcc_of_le hs] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    have h := (hasDerivAt_log ht0.ne').log hl
    convert h using 1
    rw [show (2 * (-1 / 2 : ℝ)) = -1 by norm_num, rpow_neg_one]
  have hc : ContinuousOn (fun t : ℝ => t ^ (2 * (-1 / 2 : ℝ)) / log t) (uIcc 2 √x) := by
    rw [uIcc_of_le hs]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ((continuousAt_id.rpow_const (Or.inl ht0.ne')).div (continuousAt_log ht0.ne')
      hl).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

theorem log_log_sqrt {x : ℝ} (hx : 1 < x) : log (log √x) = log (log x) - log 2 := by
  have hl : 0 < log x := log_pos hx
  rw [log_sqrt (by linarith), log_div hl.ne' (by norm_num)]

/-- `B_{−½}(x) = ½ log log x + O(1)`. -/
theorem biasTerm_critical_isBigO :
    (fun x : ℝ => biasTerm (-1 / 2) x - 1 / 2 * log (log x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have h : (fun _ : ℝ => -(1 / 2) * (log 2 + log (log 2))) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_const _ one_ne_zero _
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 4] with x hx
  rw [biasTerm_critical hx, log_log_sqrt (by linarith)]
  ring

/-- **Remark 1, Mertens.** `½ Σ_{p≤√x} 1/p = ½ log log x + O(1)`. -/
theorem half_sum_primes_isBigO (hM : Mertens2) :
    (fun x : ℝ => 1 / 2 * (∑ p ∈ (Finset.range (⌊√x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p) -
      1 / 2 * log (log x)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  obtain ⟨B, hB⟩ := hM
  have h := hB.comp_tendsto tendsto_sqrt_atTop
  have hO : (fun y : ℝ => 1 / log y) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    have : Tendsto (fun y : ℝ => 1 / log y) atTop (𝓝 0) := by
      exact tendsto_log_atTop.inv_tendsto_atTop.congr fun y => by simp
    exact this.isBigO_one ℝ
  have h1 := h.trans (hO.comp_tendsto tendsto_sqrt_atTop)
  have hc : (fun _ : ℝ => B - log 2) =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_const _ one_ne_zero _
  have h2 := (h1.add hc).const_mul_left (1 / 2)
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp only [Function.comp_apply]
  rw [log_log_sqrt hx]
  ring

/-- **Remark 1** (deterministic term). For `a > −½`, `B_a(x) ∼ x^{a+½}/((2a+1) log x)`;
for `x ≥ 4`, `B_{−½}(x) = ½(log log √x − log log 2)`; and `B_{−½}(x) = ½ log log x + O(1)`. -/
theorem remark1_deterministic :
    (∀ a : ℝ, -1 / 2 < a →
      (biasTerm a) ~[atTop] fun x : ℝ => x ^ (a + 1 / 2) / ((2 * a + 1) * log x)) ∧
    (∀ x : ℝ, 4 ≤ x → biasTerm (-1 / 2) x = 1 / 2 * (log (log √x) - log (log 2))) ∧
    ((fun x : ℝ => biasTerm (-1 / 2) x - 1 / 2 * log (log x)) =O[atTop] (fun _ : ℝ => (1 : ℝ))) :=
  ⟨fun _ ha => biasTerm_isEquivalent ha, fun _ hx => biasTerm_critical hx, biasTerm_critical_isBigO⟩

end CpsLean
