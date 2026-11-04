module

public import CpsLean.LemmaA2
set_option autoImplicit false

/-!
# Lemma A, third part: the bounds

With `v = 5/2`, `T = e^Y`, `κ = a + ½`, for `2 ≤ Y`, `3 ≤ x ≤ e^Y`:

* `psiRem_le'`: `‖G(t)‖ ≤ C (4 t Y² e^{−Y} + log t + 1)`, for `v ≤ t ≤ x`.
* `fw_mul_psiRem_le`, `integral_fw'_mul_psiRem_le`: the two terms with `G`.
* `sum_zeros_lower_le`: the lower boundary of the zero terms is `O(1)` uniformly in `T`.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

theorem re_eq_half (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) : ρ.re = 1 / 2 := by
  refine hRH ρ hρ.1 ?_ (ne_one_of_mem hρ)
  rintro ⟨n, rfl⟩
  have h := hρ.2.1
  simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re,
    Complex.re_ofNat, Complex.neg_im, Complex.im_ofNat, Complex.add_im, Complex.natCast_im,
    Complex.one_im, neg_zero, zero_mul, sub_zero, add_zero] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem one_lt_log_three : 1 < log (3 : ℝ) := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem sq_exp_le {Y : ℝ} (hY : 0 ≤ Y) : Y ^ 2 * exp (-Y) ≤ 16 := by
  have h1 : Y / 4 + 1 ≤ exp (Y / 4) := add_one_le_exp _
  have h2 : Y / 4 ≤ exp (Y / 4) := by linarith
  have h3 : (Y / 4) ^ 2 ≤ exp (Y / 4) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have h4 : exp (Y / 4) ^ 2 = exp (Y / 2) := by
    rw [← exp_nat_mul]
    congr 1
    push_cast
    ring
  have h5 : exp (Y / 2) * exp (-Y) ≤ 1 := by
    rw [← exp_add]
    apply exp_le_one_iff.mpr
    linarith
  have h6 : (0 : ℝ) < exp (-Y) := exp_pos _
  rw [h4] at h3
  nlinarith

/-- The remainder on `[5/2, x]`, with `x ≤ T = e^Y`. -/
theorem psiRem_le' (hE : TruncatedExplicitFormula) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y x t : ℝ, 2 ≤ Y → x ≤ exp Y → 5 / 2 ≤ t → t ≤ x →
      ‖psiRem (exp Y) t‖ ≤ C * (4 * t * (Y ^ 2 * exp (-Y)) + log t + 1) := by
  obtain ⟨C, hC, h⟩ := psiRem_le hE
  refine ⟨C, hC, fun Y x t hY hx ht htx => ?_⟩
  have ht0 : 0 < t := by linarith
  have hT : (2 : ℝ) ≤ exp Y := by
    have := add_one_le_exp Y
    linarith
  refine (h t (exp Y) (by linarith) hT).trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hlt : log t ≤ Y := by
    rw [log_le_iff_le_exp ht0]
    linarith
  have hlt0 : 0 ≤ log t := log_nonneg (by linarith)
  have hlog : log (t * exp Y) = log t + Y := by
    rw [log_mul ht0.ne' (exp_pos Y).ne', log_exp]
  have hsq : log (t * exp Y) ^ 2 ≤ 4 * Y ^ 2 := by
    rw [hlog]
    nlinarith
  have hdiv : t * log (t * exp Y) ^ 2 / exp Y ≤ 4 * t * (Y ^ 2 * exp (-Y)) := by
    rw [exp_neg, div_eq_mul_inv]
    have hi : 0 ≤ (exp Y)⁻¹ := by positivity
    have : t * log (t * exp Y) ^ 2 ≤ t * (4 * Y ^ 2) := mul_le_mul_of_nonneg_left hsq ht0.le
    nlinarith [mul_le_mul_of_nonneg_right this hi]
  linarith

/-- `x^c ≤ D x^κ/log² x`, for `c < κ`, `x ≥ 3`. -/
theorem rpow_le_div_log_sq {c κ : ℝ} (h : c < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 3 ≤ x → x ^ c ≤ D * (x ^ κ / log x ^ 2) := by
  obtain ⟨D, hD, hb⟩ := log_pow_le_rpow 2 (sub_pos.mpr h)
  refine ⟨D, hD, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have hk : x ^ κ = x ^ c * x ^ (κ - c) := by
    rw [← rpow_add hx0]
    ring_nf
  rw [hk]
  have h1 := hb x (by linarith)
  have hc : 0 < x ^ c := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]

/-- `x^{a+1} e^{−Y} ≤ x^{a+½} e^{−Y/2}`, for `x ≤ e^Y`. -/
theorem rpow_mul_exp_le {a x Y : ℝ} (hx0 : 0 < x) (hx : x ≤ exp Y) :
    x ^ (a + 1) * exp (-Y) ≤ x ^ (a + 1 / 2) * exp (-Y / 2) := by
  have h1 : x ^ (a + 1) = x ^ (a + 1 / 2) * x ^ ((1 : ℝ) / 2) := by
    rw [← rpow_add hx0]
    ring_nf
  have h2 : x ^ ((1 : ℝ) / 2) ≤ exp (Y / 2) := by
    calc x ^ ((1 : ℝ) / 2) ≤ (exp Y) ^ ((1 : ℝ) / 2) := by gcongr
      _ = exp (Y / 2) := by
        rw [← exp_mul]
        ring_nf
  have h3 : exp (Y / 2) * exp (-Y) = exp (-Y / 2) := by
    rw [← exp_add]
    ring_nf
  rw [h1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← h3]
  exact mul_le_mul_of_nonneg_right h2 (exp_pos _).le

theorem fw_pos (a : ℝ) {t : ℝ} (ht : 1 < t) : 0 < fw a t := by
  unfold fw
  have := log_pos ht
  positivity

/-- The term `f(x) G(x)`. -/
theorem fw_mul_psiRem_le (hE : TruncatedExplicitFormula) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y x : ℝ, 2 ≤ Y → 3 ≤ x → x ≤ exp Y →
      ‖((fw a x : ℝ) : ℂ) * psiRem (exp Y) x‖ ≤
        C * (x ^ (a + 1 / 2) / log x ^ 2 + Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) := by
  obtain ⟨CG, hCG, hG⟩ := psiRem_le' hE
  obtain ⟨D, hD, hDb⟩ := rpow_le_div_log_sq (c := a) (κ := a + 1 / 2) (by linarith)
  refine ⟨CG * (4 + 2 * D), by positivity, fun Y x hY hx hxY => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl1 : 1 < log x := one_lt_log_three.trans_le (log_le_log (by norm_num) hx)
  have hl : 0 < log x := by linarith
  have hb := hG Y x x hY hxY (by linarith) le_rfl
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fw_pos a (by linarith)).le]
  have hfw : fw a x = x ^ a / log x := rfl
  have hxa : x * x ^ a = x ^ (a + 1) := by
    rw [rpow_add_one hx0.ne']
    ring
  have hexp := rpow_mul_exp_le (a := a) hx0 hxY
  have hEx : 0 ≤ x ^ (a + 1 / 2) / log x ^ 2 := by positivity
  have hEy : 0 ≤ Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x) := by positivity
  have hxa0 : 0 < x ^ a := by positivity
  have h1 : x ^ a / log x * (4 * x * (Y ^ 2 * exp (-Y))) ≤
      4 * (Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) := by
    have hY2 : 0 ≤ Y ^ 2 := by positivity
    have : x ^ a / log x * (4 * x * (Y ^ 2 * exp (-Y))) =
        4 * (Y ^ 2 * ((x * x ^ a) * exp (-Y)) / log x) := by ring
    rw [this, hxa]
    have h2 : Y ^ 2 * (x ^ (a + 1) * exp (-Y)) / log x ≤
        Y ^ 2 * (x ^ (a + 1 / 2) * exp (-Y / 2)) / log x := by
      gcongr
    have h3 : Y ^ 2 * (x ^ (a + 1 / 2) * exp (-Y / 2)) / log x =
        Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x) := by ring
    linarith
  have h2 : x ^ a / log x * log x = x ^ a := by field_simp
  have h3 : x ^ a / log x * 1 ≤ x ^ a := by
    rw [mul_one]
    exact div_le_self hxa0.le hl1.le
  have h4 := hDb x hx
  calc fw a x * ‖psiRem (exp Y) x‖
      ≤ fw a x * (CG * (4 * x * (Y ^ 2 * exp (-Y)) + log x + 1)) :=
        mul_le_mul_of_nonneg_left hb (fw_pos a (by linarith)).le
    _ = CG * (x ^ a / log x * (4 * x * (Y ^ 2 * exp (-Y))) + x ^ a / log x * log x +
          x ^ a / log x * 1) := by rw [hfw]; ring
    _ ≤ CG * (4 * (Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) + x ^ a + x ^ a) := by
        refine mul_le_mul_of_nonneg_left ?_ hCG
        rw [h2]
        linarith
    _ ≤ CG * (4 * (Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) +
          2 * (D * (x ^ (a + 1 / 2) / log x ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCG
        linarith
    _ ≤ CG * (4 + 2 * D) * (x ^ (a + 1 / 2) / log x ^ 2 +
          Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) := by
        have h5 : 0 ≤ 2 * D * (Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) := by positivity
        have h6 : 0 ≤ 4 * (x ^ (a + 1 / 2) / log x ^ 2) := by positivity
        rw [mul_assoc CG]
        refine mul_le_mul_of_nonneg_left ?_ hCG
        nlinarith

/-- `|f′(t)| ≤ (|a| + 1/log(5/2)) t^{a−1}/log t`, for `t ≥ 5/2`. -/
theorem abs_fw'_le_div {a t : ℝ} (ht : 5 / 2 ≤ t) :
    |fw' a t| ≤ (|a| + 1 / log (5 / 2)) * (t ^ (a - 1) / log t) := by
  have ht0 : 0 < t := by linarith
  have hl0 := log_five_half_pos
  have hl1 : log (5 / 2) ≤ log t := log_le_log (by norm_num) ht
  have hl : 0 < log t := by linarith
  unfold fw'
  rw [abs_mul, abs_of_pos (show 0 < t ^ (a - 1) by positivity)]
  have h1 : |a / log t - 1 / log t ^ 2| ≤ (|a| + 1 / log (5 / 2)) / log t := by
    have h2 : a / log t - 1 / log t ^ 2 = (a - 1 / log t) / log t := by field_simp
    rw [h2, abs_div, abs_of_pos hl]
    refine div_le_div_of_nonneg_right ?_ hl.le
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le hl0 hl1
  calc t ^ (a - 1) * |a / log t - 1 / log t ^ 2|
      ≤ t ^ (a - 1) * ((|a| + 1 / log (5 / 2)) / log t) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (|a| + 1 / log (5 / 2)) * (t ^ (a - 1) / log t) := by ring

theorem continuousOn_rpow_div_log_pow (b : ℝ) (k : ℕ) {x : ℝ} :
    ContinuousOn (fun t : ℝ => t ^ (b - 1) / log t ^ k) (Set.Icc (5 / 2) x) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  exact ((continuousAt_id.rpow_const (Or.inl ht0.ne')).div
    ((continuousAt_log ht0.ne').pow k) (pow_ne_zero k (log_pos ht1).ne')).continuousWithinAt

/-- The term `∫_v^x f′ G`. -/
theorem integral_fw'_mul_psiRem_le (hE : TruncatedExplicitFormula) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y x : ℝ, 2 ≤ Y → 3 ≤ x → x ≤ exp Y →
      ‖∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * psiRem (exp Y) t‖ ≤
        C * (x ^ (a + 1 / 2) / log x ^ 2 + Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x)) := by
  obtain ⟨CG, hCG, hG⟩ := psiRem_le' hE
  set κ := a + 1 / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set c := max a (κ / 2) with hc
  have hc0 : 0 < c := lt_max_of_lt_right (half_pos hκ0)
  have hcκ : c < κ := max_lt (by rw [hκ]; linarith) (by linarith)
  have hac : a ≤ c := le_max_left _ _
  obtain ⟨C₁, hC₁, hI1⟩ := integral_rpow_div_log_pow_le (b := a + 1) (by linarith) 1
  obtain ⟨C₀, hC₀, hI0⟩ := integral_rpow_div_log_pow_le hc0 0
  obtain ⟨D, hD, hDb⟩ := rpow_le_div_log_sq hcκ
  set K₁ := |a| + 1 / log (5 / 2) with hK₁
  have hv₀ := log_five_half_pos
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₂ := 1 + 1 / log (5 / 2) with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  refine ⟨K₁ * CG * (4 * C₁ + K₂ * C₀ * D), by positivity, fun Y x hY hx hxY => ?_⟩
  have hx0 : 0 < x := by linarith
  have hxv : (5 / 2 : ℝ) ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  set A := Y ^ 2 * exp (-Y) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the dominating function
  set g : ℝ → ℝ := fun t => K₁ * CG * (4 * A * (t ^ (a + 1 - 1) / log t ^ 1) +
      K₂ * (t ^ (c - 1) / log t ^ 0)) with hg
  have hgc : IntervalIntegrable g volume (5 / 2) x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxv]
    exact continuousOn_const.mul ((continuousOn_const.mul (continuousOn_rpow_div_log_pow (a + 1) 1)).add
      (continuousOn_const.mul (continuousOn_rpow_div_log_pow c 0)))
  have hpt : ∀ t ∈ Set.Ioc (5 / 2 : ℝ) x, ‖((fw' a t : ℝ) : ℂ) * psiRem (exp Y) t‖ ≤ g t := by
    intro t ht
    have ht1 : (5 / 2 : ℝ) ≤ t := ht.1.le
    have ht0 : 0 < t := by linarith
    have hlt0 : log (5 / 2) ≤ log t := log_le_log (by norm_num) ht1
    have hlt : 0 < log t := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_fw'_le_div (a := a) ht1
    have h2 := hG Y x t hY hxY ht1 ht.2
    have h3 : t ^ (a - 1) ≤ t ^ (c - 1) :=
      rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have htp : t * t ^ (a - 1) = t ^ a := by
      rw [rpow_sub_one ht0.ne']
      field_simp
    have hinv : 1 / log t ≤ 1 / log (5 / 2) := one_div_le_one_div_of_le hv₀ hlt0
    have hmain : t ^ (a - 1) / log t * (4 * t * A + log t + 1) ≤
        4 * A * (t ^ a / log t) + K₂ * t ^ (c - 1) := by
      have e : t ^ (a - 1) / log t * (4 * t * A + log t + 1) =
          4 * A * ((t * t ^ (a - 1)) / log t) + t ^ (a - 1) * (1 + 1 / log t) := by
        field_simp
        ring
      rw [e, htp]
      have : t ^ (a - 1) * (1 + 1 / log t) ≤ t ^ (c - 1) * K₂ := by
        apply mul_le_mul h3 (by rw [hK₂]; linarith) (by positivity) (by positivity)
      linarith
    have hg' : g t = K₁ * CG * (4 * A * (t ^ a / log t) + K₂ * t ^ (c - 1)) := by
      simp only [hg, add_sub_cancel_right, pow_one, pow_zero, div_one]
    rw [hg']
    calc |fw' a t| * ‖psiRem (exp Y) t‖
        ≤ (K₁ * (t ^ (a - 1) / log t)) * (CG * (4 * t * A + log t + 1)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = K₁ * CG * (t ^ (a - 1) / log t * (4 * t * A + log t + 1)) := by ring
      _ ≤ K₁ * CG * (4 * A * (t ^ a / log t) + K₂ * t ^ (c - 1)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hxv
    (Filter.Eventually.of_forall hpt) hgc
  have hgint : ∫ t in (5 / 2 : ℝ)..x, g t = K₁ * CG * (4 * A *
      (∫ t in (5 / 2 : ℝ)..x, t ^ (a + 1 - 1) / log t ^ 1) +
      K₂ * ∫ t in (5 / 2 : ℝ)..x, t ^ (c - 1) / log t ^ 0) := by
    have i1 : IntervalIntegrable (fun t : ℝ => t ^ (a + 1 - 1) / log t ^ 1) volume (5 / 2) x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hxv]
      exact continuousOn_rpow_div_log_pow (a + 1) 1
    have i0 : IntervalIntegrable (fun t : ℝ => t ^ (c - 1) / log t ^ 0) volume (5 / 2) x := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hxv]
      exact continuousOn_rpow_div_log_pow c 0
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i1.const_mul _)
      (i0.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  refine hnorm.trans ?_
  rw [hgint]
  have b1 := hI1 x hx
  have b0 := hI0 x hx
  simp only [pow_one, pow_zero, div_one] at b1 b0 ⊢
  have hexp := rpow_mul_exp_le (a := a) hx0 hxY
  set Ex := x ^ κ / log x ^ 2 with hEx
  set Ey := Y ^ 2 * exp (-Y / 2) * (x ^ κ / log x) with hEy
  have hEx0 : 0 ≤ Ex := by positivity
  have hEy0 : 0 ≤ Ey := by positivity
  have t1 : A * (C₁ * (x ^ (a + 1) / log x)) ≤ C₁ * Ey := by
    have : A * (C₁ * (x ^ (a + 1) / log x)) = C₁ * (Y ^ 2 * (x ^ (a + 1) * exp (-Y)) / log x) := by
      rw [hA]; ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    have e : Ey = Y ^ 2 * (x ^ κ * exp (-Y / 2)) / log x := by rw [hEy]; ring
    rw [e]
    gcongr
  have t0 : C₀ * x ^ c ≤ C₀ * (D * Ex) := mul_le_mul_of_nonneg_left (hDb x hx) hC₀
  have hsum : 4 * A * (∫ t in (5 / 2 : ℝ)..x, t ^ (a + 1 - 1) / log t) +
      K₂ * ∫ t in (5 / 2 : ℝ)..x, t ^ (c - 1) ≤ 4 * (C₁ * Ey) + K₂ * (C₀ * (D * Ex)) := by
    have u1 : 4 * A * (∫ t in (5 / 2 : ℝ)..x, t ^ (a + 1 - 1) / log t) ≤
        4 * (A * (C₁ * (x ^ (a + 1) / log x))) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left b1 hA0
    have u0 : K₂ * ∫ t in (5 / 2 : ℝ)..x, t ^ (c - 1) ≤ K₂ * (C₀ * (D * Ex)) :=
      mul_le_mul_of_nonneg_left (b0.trans t0) hK₂0
    linarith
  calc K₁ * CG * (4 * A * (∫ t in (5 / 2 : ℝ)..x, t ^ (a + 1 - 1) / log t) +
        K₂ * ∫ t in (5 / 2 : ℝ)..x, t ^ (c - 1))
      ≤ K₁ * CG * (4 * (C₁ * Ey) + K₂ * (C₀ * (D * Ex))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ K₁ * CG * (4 * C₁ + K₂ * C₀ * D) * (Ex + Ey) := by
        have hK : 0 ≤ K₁ * CG := by positivity
        rw [mul_assoc (K₁ * CG)]
        refine mul_le_mul_of_nonneg_left ?_ hK
        have h1 : 0 ≤ 4 * C₁ * Ex := by positivity
        have h2 : 0 ≤ K₂ * C₀ * D * Ey := by positivity
        nlinarith

end CpsLean
