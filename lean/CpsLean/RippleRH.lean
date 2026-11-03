module

public import CpsLean.Ripple
public import CpsLean.Asymp
public import LeanBase.Hypotheses
public import CpsLean.PNTConseq
public import Mathlib.NumberTheory.AbelSummation
set_option autoImplicit false

/-!
# Weighted prime sums under the Riemann hypothesis: Proposition 3(a) and Theorem 3, Step 2

* `thetaPow b y = θ_b(y) = Σ_{p ≤ y} p^b` (Section 9.2, for real `b`).
* `thetaPow_eq`: Abel summation with the weights `log p`: for `y ≥ 2`, with `f(t) = t^b / log t`
  and `E(t) = θ(t) − t`,
  `θ_b(y) = ∫_2^y f + 2 f(2) + f(y) E(y) − ∫_2^y f′ E`.
* `theta_sub_isBigO`: under `LeanBase.VonKochPsi` and the Riemann hypothesis, `θ(x) − x = O(√x log² x)`
  (with `ψ − θ = O(√x)` from Mathlib).
* `prop3a_RH_imp_ripple`: **Proposition 3(a)**.
* `step2_bias_layer`: **Theorem 3, Step 2** (the boxed formula), for every real `a > −½`.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- `θ_b(y) = Σ_{p ≤ y} p^b` (Section 9.2), for real `b`. -/
noncomputable def thetaPow (b y : ℝ) : ℝ := ∑ p ∈ (Finset.Icc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ b

/-- `f_b(t) = t^b / log t`. -/
noncomputable def fw (b t : ℝ) : ℝ := t ^ b / log t

/-- `f_b′(t) = t^{b−1} (b / log t − 1 / log² t)`. -/
noncomputable def fw' (b t : ℝ) : ℝ := t ^ (b - 1) * (b / log t - 1 / log t ^ 2)

theorem hasDerivAt_fw (b : ℝ) {t : ℝ} (ht : 1 < t) : HasDerivAt (fw b) (fw' b t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < log t := log_pos ht
  have h := (hasDerivAt_rpow_const (p := b) (Or.inl ht0.ne')).div (hasDerivAt_log ht0.ne') hl.ne'
  convert h using 1
  · funext s; rfl
  · unfold fw'
    rw [rpow_sub_one ht0.ne']
    field_simp

theorem continuousOn_fw' (b : ℝ) : ContinuousOn (fw' b) (Ici 2) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ht
  have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
  have : ContinuousAt (fw' b) t := by
    unfold fw'
    exact ((continuousAt_id.rpow_const (Or.inl (by simp; linarith))).mul
      ((continuousAt_const.div (continuousAt_log (by linarith)) hl).sub
        (continuousAt_const.div ((continuousAt_log (by linarith)).pow 2) (pow_ne_zero 2 hl))))
  exact this.continuousWithinAt

theorem continuousOn_fw (b : ℝ) : ContinuousOn (fw b) (Ici 2) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ht
  exact (hasDerivAt_fw b (by linarith)).continuousAt.continuousWithinAt

theorem sum_thetaCoeff (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (if k.Prime then log k else 0) = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter]

theorem intervalIntegrable_theta (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
  Chebyshev.theta_mono.intervalIntegrable

/-- **Abel summation** with the weights `log p`: for `y ≥ 2`,
`θ_b(y) = ∫_2^y f + 2 f(2) + f(y) (θ(y) − y) − ∫_2^y f′ (θ − id)`. -/
theorem thetaPow_eq (b : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    thetaPow b y = (∫ t in (2 : ℝ)..y, fw b t) + 2 * fw b 2 + fw b y * (Chebyshev.theta y - y) -
      ∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t) := by
  set c : ℕ → ℝ := fun k => if k.Prime then log k else 0
  have hc0 : c 0 = 0 := by simp [c, Nat.not_prime_zero]
  have hc1 : c 1 = 0 := by simp [c, Nat.not_prime_one]
  have hderiv : ∀ t ∈ Set.Icc 2 y, deriv (fw b) t = fw' b t := fun t ht =>
    (hasDerivAt_fw b (by linarith [ht.1])).deriv
  have hfi : IntervalIntegrable (fw' b) volume 2 y := intervalIntegrable_of_Ici (continuousOn_fw' b) le_rfl hy
  have h := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 y
    (fun t ht => (hasDerivAt_fw b (by linarith [ht.1])).differentiableAt)
    (by
      refine (((continuousOn_fw' b).mono fun t (ht : t ∈ Set.Icc (2 : ℝ) y) =>
        (ht.1 : (2 : ℝ) ≤ t)).integrableOn_compact isCompact_Icc).congr_fun
        (fun t ht => (hderiv t ht).symm) measurableSet_Icc)
  -- the left side is `θ_b(y)`
  have hl : ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, fw b k * c k = thetaPow b y := by
    unfold thetaPow; rw [sum_filter]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : k.Prime
    · have : (1 : ℝ) < k := by exact_mod_cast hk.one_lt
      simp only [c, if_pos hk, fw]; field_simp [(log_pos this).ne']
    · simp [c, hk]
  have hθ : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := fun t => by
    rw [sum_thetaCoeff, ← Chebyshev.theta_eq_theta_coe_floor]
  simp only [hθ, hl] at h
  rw [h]
  -- the integral, with `deriv f = f′` on `(2, y]`
  have hI : ∫ t in Set.Ioc 2 y, deriv (fw b) t * Chebyshev.theta t =
      ∫ t in (2 : ℝ)..y, fw' b t * Chebyshev.theta t := by
    rw [intervalIntegral.integral_of_le hy]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [hderiv t ⟨ht.1.le, ht.2⟩]
  rw [hI]
  -- `∫_2^y f′ · t = y f(y) − 2 f(2) − ∫_2^y f`
  have hg : ∀ t ∈ uIcc (2 : ℝ) y, HasDerivAt (fun s => s * fw b s) (fw b t + t * fw' b t) t := by
    intro t ht; rw [uIcc_of_le hy] at ht
    have := (hasDerivAt_id' t).mul (hasDerivAt_fw b (by linarith [ht.1]))
    convert this using 1; ring
  have hfw := intervalIntegrable_of_Ici (continuousOn_fw b) le_rfl hy
  have hmul : IntervalIntegrable (fun t => t * fw' b t) volume 2 y :=
    ((continuousOn_id.mul (continuousOn_fw' b)).mono fun t ht => by
      rw [uIcc_of_le hy] at ht; exact ht.1).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg (hfw.add hmul)
  rw [intervalIntegral.integral_add hfw hmul] at hftc
  have hθi : IntervalIntegrable (fun t => fw' b t * Chebyshev.theta t) volume 2 y :=
    ((intervalIntegrable_theta 2 y).continuousOn_mul (by
      rw [uIcc_of_le hy]; exact (continuousOn_fw' b).mono fun t ht => ht.1))
  have hsplit : ∫ t in (2 : ℝ)..y, fw' b t * Chebyshev.theta t =
      (∫ t in (2 : ℝ)..y, t * fw' b t) + ∫ t in (2 : ℝ)..y, fw' b t * (Chebyshev.theta t - t) := by
    have h2 : IntervalIntegrable (fun t => fw' b t * (Chebyshev.theta t - t)) volume 2 y :=
      (hθi.sub hmul).congr fun t _ => by ring
    rw [← intervalIntegral.integral_add hmul h2]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [hsplit]
  linarith

/-! ### Uniform bounds for `θ(t) − t` -/

/-- An `O`-bound at `+∞` becomes a bound on `[2, ∞)` when the function is locally bounded and the
comparison function is bounded below by a positive constant. -/
theorem uniform_of_isBigO {E g : ℝ → ℝ} {g₀ : ℝ} (hE : E =O[atTop] g) (hg₀ : 0 < g₀)
    (hg : ∀ t, 2 ≤ t → g₀ ≤ g t) (hloc : ∀ T, ∃ M, ∀ t, 2 ≤ t → t ≤ T → |E t| ≤ M) :
    ∃ C, 0 ≤ C ∧ ∀ t, 2 ≤ t → |E t| ≤ C * g t := by
  obtain ⟨c, hc⟩ := hE.bound
  obtain ⟨T, hT⟩ := eventually_atTop.1 hc
  obtain ⟨M, hM⟩ := hloc T
  refine ⟨max c 0 + |M| / g₀, by positivity, fun t ht => ?_⟩
  have hgt : 0 < g t := hg₀.trans_le (hg t ht)
  by_cases htT : T ≤ t
  · have := hT t htT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgt] at this
    have : c * g t ≤ (max c 0 + |M| / g₀) * g t := by
      gcongr; linarith [le_max_left c 0, div_nonneg (abs_nonneg M) hg₀.le]
    linarith
  · push Not at htT
    have h1 := hM t ht htT.le
    have h2 : |M| ≤ |M| / g₀ * g t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hg₀]
      exact mul_le_mul_of_nonneg_left (hg t ht) (abs_nonneg M)
    have h3 : |M| / g₀ * g t ≤ (max c 0 + |M| / g₀) * g t := by
      gcongr; linarith [le_max_right c 0]
    linarith [le_abs_self M]

/-- `|θ(t) − t| ≤ (log 4 + 1) T` on `[2, T]`. -/
theorem theta_sub_loc (T : ℝ) : ∃ M, ∀ t, 2 ≤ t → t ≤ T → |Chebyshev.theta t - t| ≤ M := by
  refine ⟨(log 4 + 1) * T, fun t ht htT => ?_⟩
  have h0 := Chebyshev.theta_nonneg t
  have h1 := Chebyshev.theta_le_log4_mul_x (show 0 ≤ t by linarith)
  have hl4 : 0 ≤ log 4 := log_nonneg (by norm_num)
  rw [abs_le]; constructor <;> nlinarith

/-- Under von Koch's theorem and the Riemann hypothesis, `θ(x) − x = O(√x log² x)`. -/
theorem theta_sub_isBigO (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) :
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] (fun x : ℝ => √x * log x ^ 2) := by
  have h1 := hK hRH
  have h2 : (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x) =O[atTop]
      (fun x : ℝ => √x * log x ^ 2) := by
    refine Chebyshev.isBigO_psi_sub_theta_sqrt.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 3] with x hx
    have hl : 1 ≤ log x := by
      rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg x),
      abs_of_nonneg (by positivity), one_mul]
    exact le_mul_of_one_le_right (sqrt_nonneg x) (by nlinarith)
  exact (h1.sub h2).congr_left fun x => by ring

/-- The uniform form: `|θ(t) − t| ≤ C √t log² t` for every `t ≥ 2`. -/
theorem theta_sub_le (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) :
    ∃ C, 0 ≤ C ∧ ∀ t, 2 ≤ t → |Chebyshev.theta t - t| ≤ C * (√t * log t ^ 2) := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine uniform_of_isBigO (theta_sub_isBigO hK hRH) (g₀ := √2 * log 2 ^ 2) (by positivity)
    (fun t ht => ?_) theta_sub_loc
  exact mul_le_mul (sqrt_le_sqrt ht) (pow_le_pow_left₀ hl2.le (log_le_log (by norm_num) ht) 2)
    (by positivity) (sqrt_nonneg _)

/-! ### Proposition 3(a) -/

theorem thetaPow_one (y : ℝ) : thetaPow 1 y = sumPrimes y := by
  simp [thetaPow, sumPrimes]

theorem fw_one (t : ℝ) : fw 1 t = t / log t := by simp [fw]

theorem abs_fw'_one_le {t : ℝ} (ht : 2 ≤ t) : |fw' 1 t| ≤ (1 + 1 / log 2) / log t := by
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl : log 2 ≤ log t := log_le_log (by norm_num) ht
  have hlt : 0 < log t := by linarith
  unfold fw'
  rw [sub_self, rpow_zero, one_mul, abs_le]
  have : 1 / log t ^ 2 ≤ (1 / log 2) / log t := by
    rw [div_div, one_div_le_one_div (by positivity) (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hl hlt.le
  have : 0 ≤ 1 / log t ^ 2 := by positivity
  constructor
  · have : (1 : ℝ) / log t ≥ 0 := by positivity
    have : -((1 + 1 / log 2) / log t) = -(1 / log t) - (1 / log 2) / log t := by ring
    linarith
  · have : (1 + 1 / log 2) / log t = 1 / log t + (1 / log 2) / log t := by ring
    linarith

/-- `S(x) − B(x) = Σ_{p ≤ x} p − ∫_2^x t dt / log t` for `x ≥ 2`. -/
theorem Sx_sub_B {x : ℝ} (hx : 2 ≤ x) : Sx x - B x = sumPrimes x - ∫ t in (2 : ℝ)..x, t / log t := by
  rw [Sx, B, integral_inv_log_sq hx, S_eq_sumPrimes]
  have : sumPrimes (⌊x⌋₊ : ℝ) = sumPrimes x := by unfold sumPrimes; rw [Nat.floor_natCast]
  rw [this]; ring

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add' hx (by norm_num), rpow_one, sqrt_eq_rpow]

/-- Under von Koch's theorem and the Riemann hypothesis, `S(x) − B(x) = O(x^{3/2} log x)`. -/
theorem S_sub_B_isBigO (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) :
    (fun x : ℝ => Sx x - B x) =O[atTop] (fun x : ℝ => x ^ ((3 : ℝ) / 2) * log x) := by
  obtain ⟨C, hC0, hC⟩ := theta_sub_le hK hRH
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  set K := (1 + 1 / log 2) * C
  have hK0 : 0 ≤ K := by positivity
  refine IsBigO.of_bound (C + K + 2 * |fw 1 2|) ?_
  filter_upwards [eventually_ge_atTop 3] with x hx
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlx : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
  have hsx : 0 ≤ √x := sqrt_nonneg x
  have hP : 1 ≤ x * √x * log x := by
    have : 1 ≤ √x := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by linarith)
    have : 1 ≤ x * √x := one_le_mul_of_one_le_of_one_le (by linarith) this
    exact one_le_mul_of_one_le_of_one_le this hlx
  rw [Sx_sub_B hx2, Real.norm_eq_abs, Real.norm_eq_abs,
    rpow_three_halves (by linarith), abs_of_nonneg (show (0 : ℝ) ≤ x * √x * log x by linarith)]
  -- the three error terms
  have e1 : |fw 1 x * (Chebyshev.theta x - x)| ≤ C * (x * √x * log x) := by
    rw [abs_mul, fw_one, abs_of_nonneg (div_nonneg (by linarith) (by linarith))]
    calc x / log x * |Chebyshev.theta x - x| ≤ x / log x * (C * (√x * log x ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC x hx2) (div_nonneg (by linarith) (by linarith))
      _ = C * (x * √x * log x) := by field_simp
  have e2 : |∫ t in (2 : ℝ)..x, fw' 1 t * (Chebyshev.theta t - t)| ≤ K * (x * √x * log x) := by
    have hb : ∀ t ∈ uIoc (2 : ℝ) x, ‖fw' 1 t * (Chebyshev.theta t - t)‖ ≤ K * (√x * log x) := by
      intro t ht
      rw [uIoc_of_le hx2] at ht
      have ht2 : 2 ≤ t := ht.1.le
      have hlt : 0 < log t := log_pos (by linarith)
      rw [Real.norm_eq_abs, abs_mul]
      calc |fw' 1 t| * |Chebyshev.theta t - t| ≤ (1 + 1 / log 2) / log t * (C * (√t * log t ^ 2)) :=
            mul_le_mul (abs_fw'_one_le ht2) (hC t ht2) (abs_nonneg _) (by positivity)
        _ = K * (√t * log t) := by simp only [K]; field_simp
        _ ≤ K * (√x * log x) := mul_le_mul_of_nonneg_left (mul_le_mul (sqrt_le_sqrt ht.2)
            (log_le_log (by linarith) ht.2) hlt.le (sqrt_nonneg _)) hK0
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 2)] at this
    calc _ ≤ K * (√x * log x) * (x - 2) := this
      _ ≤ K * (x * √x * log x) := by nlinarith [mul_nonneg hK0 (mul_nonneg hsx (by linarith : (0 : ℝ) ≤ log x))]
  have e3 : |2 * fw 1 2| ≤ 2 * |fw 1 2| * (x * √x * log x) := by
    rw [abs_mul, abs_two]; nlinarith [abs_nonneg (fw 1 2)]
  have : sumPrimes x - ∫ t in (2 : ℝ)..x, t / log t = 2 * fw 1 2 + fw 1 x * (Chebyshev.theta x - x) -
      ∫ t in (2 : ℝ)..x, fw' 1 t * (Chebyshev.theta t - t) := by
    rw [← thetaPow_one, thetaPow_eq 1 hx2]
    simp only [fw_one]; ring
  rw [this]
  calc |2 * fw 1 2 + fw 1 x * (Chebyshev.theta x - x) -
          ∫ t in (2 : ℝ)..x, fw' 1 t * (Chebyshev.theta t - t)|
    _ ≤ |2 * fw 1 2| + |fw 1 x * (Chebyshev.theta x - x)| +
          |∫ t in (2 : ℝ)..x, fw' 1 t * (Chebyshev.theta t - t)| := by
        refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ (C + K + 2 * |fw 1 2|) * (x * √x * log x) := by nlinarith

/-- `|log a − log b| ≤ |a − b| / min(a, b)` for `a, b > 0`. -/
theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |log a - log b| ≤ |a - b| / min a b := by
  have hm : 0 < min a b := lt_min ha hb
  rw [abs_le]
  constructor
  · have h := log_le_sub_one_of_pos (div_pos hb ha)
    rw [log_div hb.ne' ha.ne'] at h
    have : b / a - 1 = (b - a) / a := by field_simp
    have : (b - a) / a ≤ |a - b| / min a b := by
      rw [abs_sub_comm]
      exact div_le_div₀ (abs_nonneg _) (le_abs_self _) hm (min_le_left _ _)
    linarith
  · have h := log_le_sub_one_of_pos (div_pos ha hb)
    rw [log_div ha.ne' hb.ne'] at h
    have : a / b - 1 = (a - b) / b := by field_simp
    have : (a - b) / b ≤ |a - b| / min a b :=
      div_le_div₀ (abs_nonneg _) (le_abs_self _) hm (min_le_right _ _)
    linarith

/-- `B(x) ≥ x² / (4 log x)` for `x ≥ 4`. -/
theorem B_ge {x : ℝ} (hx : 4 ≤ x) : x ^ 2 / (4 * log x) ≤ B x := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  rw [B, integral_inv_log_sq hx2]
  have hi : ∀ y z : ℝ, 2 ≤ y → 2 ≤ z → IntervalIntegrable (fun t : ℝ => t / log t) volume y z :=
    fun y z hy hz => intervalIntegrable_of_Ici continuousOn_id_div_log hy hz
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 2 (x / 2) le_rfl (by linarith))
    (hi (x / 2) x (by linarith) hx2)]
  have h1 : 0 ≤ ∫ t in (2 : ℝ)..x / 2, t / log t :=
    intervalIntegral.integral_nonneg (by linarith) fun t ht =>
      div_nonneg (by linarith [ht.1]) (log_nonneg (by linarith [ht.1]))
  have h2 : ∫ t in x / 2..x, (x / 2) / log x ≤ ∫ t in x / 2..x, t / log t := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hi (x / 2) x (by linarith) hx2) fun t ht => ?_
    have htp : 0 < log t := log_pos (by linarith [ht.1])
    rw [div_le_div_iff₀ hlx htp]
    exact mul_le_mul ht.1 (log_le_log (by linarith [ht.1]) ht.2) htp.le (by linarith [ht.1])
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  have : x ^ 2 / (4 * log x) = (x - x / 2) * (x / 2 / log x) := by field_simp; ring
  linarith

/-- **Proposition 3(a).** Under the Riemann hypothesis (with von Koch's theorem),
`S(x) − B(x) = O(x^{3/2} log x)`, hence `|log S(x) − log B(x)| = O((log x)² / √x)`. -/
theorem prop3a_RH_imp_ripple (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) :
    ((fun x : ℝ => Sx x - B x) =O[atTop] (fun x : ℝ => x ^ ((3 : ℝ) / 2) * log x)) ∧
      ((fun x : ℝ => log (Sx x) - log (B x)) =O[atTop] (fun x : ℝ => log x ^ 2 / √x)) := by
  refine ⟨S_sub_B_isBigO hK hRH, ?_⟩
  obtain ⟨c, hc⟩ := (S_sub_B_isBigO hK hRH).bound
  -- `c x^{3/2} log x ≤ x² / (8 log x)` eventually
  have hsmall : ∀ᶠ x : ℝ in atTop, |c| * (x * √x * log x) ≤ x ^ 2 / (8 * log x) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 4) (by norm_num))
    have h' := (h.def (show (0 : ℝ) < 1 / (8 * (|c| + 1)) by positivity))
    filter_upwards [h', eventually_ge_atTop 4] with x hx hx4
    have hx0 : 0 < x := by linarith
    have hlx : 0 < log x := log_pos (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx,
      abs_of_pos (rpow_pos_of_pos hx0 ((1 : ℝ) / 4))] at hx
    -- `log x ≤ x^{1/4} / (8(|c|+1))`, so `log² x ≤ √x / (64 (|c|+1)²)`
    have hq : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = √x := by
      rw [← rpow_add hx0, sqrt_eq_rpow]; norm_num
    have hl2 : log x * log x ≤ √x / (8 * (|c| + 1)) ^ 2 := by
      calc log x * log x ≤ (1 / (8 * (|c| + 1)) * x ^ ((1 : ℝ) / 4)) *
            (1 / (8 * (|c| + 1)) * x ^ ((1 : ℝ) / 4)) := mul_le_mul hx hx hlx.le (by positivity)
        _ = √x / (8 * (|c| + 1)) ^ 2 := by rw [← hq]; field_simp
    have hsx : √x * √x = x := mul_self_sqrt hx0.le
    rw [le_div_iff₀ (by positivity)]
    have : |c| * (x * √x * log x) * (8 * log x) = 8 * |c| * x * √x * (log x * log x) := by ring
    rw [this]
    calc 8 * |c| * x * √x * (log x * log x) ≤ 8 * |c| * x * √x * (√x / (8 * (|c| + 1)) ^ 2) := by
          gcongr
      _ = x ^ 2 * (8 * |c| / (8 * (|c| + 1)) ^ 2) := by
          have hxx : x * √x * √x = x ^ 2 := by rw [mul_assoc, hsx]; ring
          rw [← hxx]; field_simp
      _ ≤ x ^ 2 := by
          apply mul_le_of_le_one_right (by positivity)
          rw [div_le_one (by positivity)]; nlinarith [abs_nonneg c]
  refine IsBigO.of_bound (8 * |c|) ?_
  filter_upwards [hc, hsmall, eventually_ge_atTop 4] with x hxc hxs hx4
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos (by linarith)
  have hBge := B_ge hx4
  have hBpos : 0 < B x := lt_of_lt_of_le (by positivity) hBge
  rw [Real.norm_eq_abs, Real.norm_eq_abs, rpow_three_halves hx0.le,
    abs_of_nonneg (show (0 : ℝ) ≤ x * √x * log x by positivity)] at hxc
  have hdiff : |Sx x - B x| ≤ |c| * (x * √x * log x) :=
    hxc.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity))
  have hSge : x ^ 2 / (8 * log x) ≤ Sx x := by
    have : x ^ 2 / (4 * log x) = 2 * (x ^ 2 / (8 * log x)) := by field_simp; ring
    have := neg_abs_le (Sx x - B x)
    linarith
  have hSpos : 0 < Sx x := lt_of_lt_of_le (by positivity) hSge
  have hmin : x ^ 2 / (8 * log x) ≤ min (Sx x) (B x) := by
    refine le_min hSge (le_trans ?_ hBge)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ log x ^ 2 / √x by positivity)]
  calc |log (Sx x) - log (B x)| ≤ |Sx x - B x| / min (Sx x) (B x) := abs_log_sub_log_le hSpos hBpos
    _ ≤ |c| * (x * √x * log x) / (x ^ 2 / (8 * log x)) :=
        div_le_div₀ (by positivity) hdiff (by positivity) hmin
    _ = 8 * |c| * (log x ^ 2 / √x) := by
        have hsx : √x * √x = x := mul_self_sqrt hx0.le
        have : 0 < √x := sqrt_pos.2 hx0
        have hxx : x ^ 2 = x * √x * √x := by rw [mul_assoc, hsx]; ring
        rw [hxx]; field_simp

end CpsLean
