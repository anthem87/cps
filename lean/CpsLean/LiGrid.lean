module

public import CpsLean.LogIntPV
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false

/-!
# Rational bounds on `li`

* `li_two_bounds`: `½ ≤ li 2 ≤ 2`, from `li_eq` and `1/log u − 1/(u − 1) ≥ ½` on `(0, 1)`.
* `li_step_lower`, `li_step_upper`: the mean value theorem, with `li′ = 1/log`.
* `liChainOk`: a check, on natural numbers, of a chain of bounds along a grid; `liChain_sound` is its
  correctness. On each cell, `log y` is compared with `(m/64) log 2` through `y⁶⁴` and `2^m`.
-/

open Real Set

@[expose] public section

namespace CpsLean

theorem liReg_half {u : ℝ} (h0 : 0 < u) (h1 : u < 1) : 1 / 2 ≤ liReg u := by
  have hw : 0 ≤ u⁻¹ - 1 := by
    have := (one_lt_inv₀ h0).mpr h1
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hw
  have e : 1 + (u⁻¹ - 1) = u⁻¹ := by ring
  rw [e, Real.log_inv] at hlog
  have hl : log u < 0 := log_neg h0 h1
  have e2 : 2 * (u⁻¹ - 1) / (u⁻¹ - 1 + 2) = 2 * (1 - u) / (1 + u) := by
    field_simp
    ring
  rw [e2] at hlog
  have hv : 0 < 1 - u := by linarith
  have hp : 0 < 2 * (1 - u) / (1 + u) := by positivity
  have h3 : 1 / (-log u) ≤ (1 + u) / (2 * (1 - u)) := by
    have := one_div_le_one_div_of_le hp hlog
    rwa [one_div_div] at this
  unfold liReg
  have e3 : 1 / log u = -(1 / (-log u)) := by
    rw [one_div, one_div, inv_neg, neg_neg]
  have e4 : 1 / (u - 1) = -(1 / (1 - u)) := by
    rw [one_div, one_div, ← inv_neg, neg_sub]
  have e5 : (1 + u) / (2 * (1 - u)) = 1 / (1 - u) - 1 / 2 := by
    field_simp
    ring
  rw [e3, e4]
  linarith

/-- `½ ≤ li 2 ≤ 2`. -/
theorem li_two_bounds : 1 / 2 ≤ li 2 ∧ li 2 ≤ 2 := by
  have h := li_eq (y := 2) (by norm_num)
  have h1 : log ((2 : ℝ) - 1) = 0 := by norm_num
  rw [h1, add_zero] at h
  have hi : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → IntervalIntegrable liReg MeasureTheory.volume p q :=
    fun hp hq => intervalIntegrable_liReg hp hq
  constructor
  · rw [h, ← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl zero_le_one)
      (hi zero_le_one zero_le_two)]
    have h2 : 0 ≤ ∫ u in (1 : ℝ)..2, liReg u :=
      intervalIntegral.integral_nonneg (by norm_num) fun u hu => (liReg_bounds (by linarith [hu.1])).1
    have h3 : 1 / 2 ≤ ∫ u in (0 : ℝ)..1, liReg u := by
      have := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := 1) (f := fun _ => (1 / 2 : ℝ))
        (g := liReg) zero_le_one intervalIntegrable_const (hi le_rfl zero_le_one)
        (fun u hu => liReg_half hu.1 hu.2)
      simpa using this
    linarith
  · rw [h]
    have := intervalIntegral.integral_mono_on (a := 0) (b := 2) (f := liReg) (g := fun _ => (1 : ℝ))
      zero_le_two (hi le_rfl zero_le_two) intervalIntegrable_const
      (fun u hu => by
        rcases eq_or_lt_of_le hu.1 with h0 | h0
        · rw [← h0]
          simp [liReg]
        · exact (liReg_bounds h0).2)
    simpa using this

theorem continuousOn_li {a b : ℝ} (ha : 1 < a) : ContinuousOn li (Icc a b) := fun y hy =>
  (hasDerivAt_li (ha.trans_le hy.1)).continuousAt.continuousWithinAt

theorem differentiableOn_li {a b : ℝ} (ha : 1 < a) : DifferentiableOn ℝ li (interior (Icc a b)) :=
  fun y hy => by
    rw [interior_Icc] at hy
    exact (hasDerivAt_li (ha.trans hy.1)).differentiableAt.differentiableWithinAt

/-- `(b − a)/c ≤ li b − li a` if `log ≤ c` on `[a, b]`. -/
theorem li_step_lower {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : log b ≤ c) :
    (b - a) / c ≤ li b - li a := by
  have hlb : 0 < log a := log_pos ha
  have hmono : log a ≤ log b := log_le_log (by linarith) hab
  have hc0 : 0 < c := by linarith
  have := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv (f := li) (continuousOn_li ha)
    (differentiableOn_li ha) (C := 1 / c) (fun y hy => by
      rw [interior_Icc] at hy
      rw [(hasDerivAt_li (ha.trans hy.1)).deriv]
      have hy0 : 1 < y := ha.trans hy.1
      refine one_div_le_one_div_of_le (log_pos hy0) ?_
      exact (log_le_log (by linarith) hy.2.le).trans hc)
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  calc (b - a) / c = 1 / c * (b - a) := by ring
    _ ≤ _ := this

/-- `li b − li a ≤ (b − a)/c` if `0 < c ≤ log` on `[a, b]`. -/
theorem li_step_upper {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc0 : 0 < c) (hc : c ≤ log a) :
    li b - li a ≤ (b - a) / c := by
  have := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le (f := li) (continuousOn_li ha)
    (differentiableOn_li ha) (C := 1 / c) (fun y hy => by
      rw [interior_Icc] at hy
      rw [(hasDerivAt_li (ha.trans hy.1)).deriv]
      have hy0 : 1 < y := ha.trans hy.1
      refine one_div_le_one_div_of_le hc0 ?_
      exact hc.trans (log_le_log (by linarith) hy.1.le))
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  calc li b - li a ≤ 1 / c * (b - a) := this
    _ = _ := by ring

theorem li_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : li a ≤ li b := by
  have h := li_step_lower ha hab le_rfl
  have hl : 0 ≤ log b := log_nonneg (by linarith)
  have : 0 ≤ (b - a) / log b := div_nonneg (by linarith) hl
  linarith

/-- The check of a chain of bounds along a grid, in units `y = b/8` and `L/10⁴`. -/
def liChainOk : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → Bool
  | _, _, _, _, [] => true
  | a, mla, L, U, (b, mu, mlb, L', U') :: xs =>
    decide (a < b) && decide (0 < mu) && decide (0 < mla) &&
      decide (b ^ 64 ≤ 2 ^ mu * 8 ^ 64) && decide (2 ^ mlb * 8 ^ 64 ≤ b ^ 64) &&
      decide (L ≤ L') && decide (U ≤ U') &&
      decide ((L' - L) * (8 * mu * 6931471808) ≤ (b - a) * 10 ^ 4 * (64 * 10 ^ 10)) &&
      decide ((b - a) * 10 ^ 4 * (64 * 10 ^ 10) ≤ (U' - U) * (8 * mla * 6931471803)) &&
      liChainOk b mlb L' U' xs

/-- A single step of the chain. -/
theorem liChain_step {a mla L U b mu mlb L' U' : ℕ} (ha8 : 8 < a) (hab : a < b) (hmu : 0 < mu)
    (hmla : 0 < mla) (h1 : b ^ 64 ≤ 2 ^ mu * 8 ^ 64) (h2 : 2 ^ mlb * 8 ^ 64 ≤ b ^ 64)
    (hL : L ≤ L') (hU : U ≤ U')
    (h3 : (L' - L) * (8 * mu * 6931471808) ≤ (b - a) * 10 ^ 4 * (64 * 10 ^ 10))
    (h4 : (b - a) * 10 ^ 4 * (64 * 10 ^ 10) ≤ (U' - U) * (8 * mla * 6931471803))
    (hlo : (L : ℝ) / 10 ^ 4 ≤ li ((a : ℝ) / 8)) (hhi : li ((a : ℝ) / 8) ≤ (U : ℝ) / 10 ^ 4)
    (hlog : (mla : ℝ) / 64 * 0.6931471803 ≤ log ((a : ℝ) / 8)) :
    (L' : ℝ) / 10 ^ 4 ≤ li ((b : ℝ) / 8) ∧ li ((b : ℝ) / 8) ≤ (U' : ℝ) / 10 ^ 4 ∧
      (mlb : ℝ) / 64 * 0.6931471803 ≤ log ((b : ℝ) / 8) := by
  have ha8' : (8 : ℝ) < a := by exact_mod_cast ha8
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hx1 : (1 : ℝ) < (a : ℝ) / 8 := by linarith
  have hxy : (a : ℝ) / 8 ≤ (b : ℝ) / 8 := by linarith
  have hy0 : (0 : ℝ) < (b : ℝ) / 8 := by linarith
  have hlu := Real.log_two_lt_d9
  have hll := Real.log_two_gt_d9
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  -- `y⁶⁴` against `2^m`
  have hpow : ((b : ℝ) / 8) ^ 64 = (b : ℝ) ^ 64 / 8 ^ 64 := div_pow _ _ _
  have h1' : ((b : ℝ) / 8) ^ 64 ≤ 2 ^ mu := by
    rw [hpow, div_le_iff₀ (by positivity)]
    exact_mod_cast h1
  have h2' : (2 : ℝ) ^ mlb ≤ ((b : ℝ) / 8) ^ 64 := by
    rw [hpow, le_div_iff₀ (by positivity)]
    exact_mod_cast h2
  have hlogU : log ((b : ℝ) / 8) ≤ (mu : ℝ) / 64 * 0.6931471808 := by
    have := log_le_log (by positivity) h1'
    rw [log_pow, log_pow] at this
    push_cast at this
    have hmu0 : (0 : ℝ) ≤ mu := Nat.cast_nonneg _
    nlinarith
  have hlogL : (mlb : ℝ) / 64 * 0.6931471803 ≤ log ((b : ℝ) / 8) := by
    have := log_le_log (by positivity) h2'
    rw [log_pow, log_pow] at this
    push_cast at this
    have hml0 : (0 : ℝ) ≤ mlb := Nat.cast_nonneg _
    nlinarith
  have hmu' : (0 : ℝ) < mu := by exact_mod_cast hmu
  have hmla' : (0 : ℝ) < mla := by exact_mod_cast hmla
  -- the steps of `li`
  have hs1 := li_step_lower hx1 hxy hlogU
  have hs2 := li_step_upper (b := (b : ℝ) / 8) hx1 hxy (by positivity) hlog
  have h3' : ((L' : ℝ) - L) * (8 * mu * 6931471808) ≤ ((b : ℝ) - a) * 10 ^ 4 * (64 * 10 ^ 10) := by
    have : (((L' - L) * (8 * mu * 6931471808) : ℕ) : ℝ) ≤
        (((b - a) * 10 ^ 4 * (64 * 10 ^ 10) : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast [Nat.cast_sub hL, Nat.cast_sub hab.le] at this
    norm_num at this ⊢
    exact this
  have h4' : ((b : ℝ) - a) * 10 ^ 4 * (64 * 10 ^ 10) ≤ ((U' : ℝ) - U) * (8 * mla * 6931471803) := by
    have : (((b - a) * 10 ^ 4 * (64 * 10 ^ 10) : ℕ) : ℝ) ≤
        (((U' - U) * (8 * mla * 6931471803) : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast [Nat.cast_sub hU, Nat.cast_sub hab.le] at this
    norm_num at this ⊢
    exact this
  refine ⟨?_, ?_, hlogL⟩
  · have hq : ((L' : ℝ) - L) / 10 ^ 4 ≤ ((b : ℝ) / 8 - (a : ℝ) / 8) / ((mu : ℝ) / 64 * 0.6931471808) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e : (L' : ℝ) / 10 ^ 4 = (L : ℝ) / 10 ^ 4 + ((L' : ℝ) - L) / 10 ^ 4 := by ring
    linarith
  · have hq : ((b : ℝ) / 8 - (a : ℝ) / 8) / ((mla : ℝ) / 64 * 0.6931471803) ≤ ((U' : ℝ) - U) / 10 ^ 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e : (U' : ℝ) / 10 ^ 4 = (U : ℝ) / 10 ^ 4 + ((U' : ℝ) - U) / 10 ^ 4 := by ring
    linarith

/-- The correctness of `liChainOk`. -/
theorem liChain_sound : ∀ (xs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (a mla L U : ℕ), 8 < a →
    (L : ℝ) / 10 ^ 4 ≤ li ((a : ℝ) / 8) → li ((a : ℝ) / 8) ≤ (U : ℝ) / 10 ^ 4 →
    (mla : ℝ) / 64 * 0.6931471803 ≤ log ((a : ℝ) / 8) → liChainOk a mla L U xs = true →
    ∀ e ∈ xs, 8 < e.1 ∧ (e.2.2.2.1 : ℝ) / 10 ^ 4 ≤ li ((e.1 : ℝ) / 8) ∧
      li ((e.1 : ℝ) / 8) ≤ (e.2.2.2.2 : ℝ) / 10 ^ 4 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨b, mu, mlb, L', U'⟩ := x
    intro a mla L U ha hlo hhi hlog hok e he
    simp only [liChainOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hmu⟩, hmla⟩, h1⟩, h2⟩, hL⟩, hU⟩, h3⟩, h4⟩, hrest⟩ := hok
    obtain ⟨hb1, hb2, hb3⟩ := liChain_step ha hab hmu hmla h1 h2 hL hU h3 h4 hlo hhi hlog
    have hb8 : 8 < b := ha.trans hab
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨hb8, hb1, hb2⟩
    · exact ih b mlb L' U' hb8 hb1 hb2 hb3 hrest e he'

end CpsLean
