module

public import CpsLean.PNTConseq
set_option autoImplicit false

/-!
# The Step Theorem and the scaling laws (Sections 3 and 5 of the paper)

From the prime number theorem (hypothesis `PNT`):

* `theorem1_i`: `Δ_m ∼ 2/m` (Theorem 1, first part);
* `theorem1_ii`: `δ(t) = (1 + o(1)) √t e^{−t/2}` (Theorem 1, second part, and the asymptotics in
  Theorem 2);
* `prop2_scaling`: `t = 2 log N − log log N − log 2 + o(1)` along `N = N(t)` (Proposition 2);
* `cor2_halfExponent`: `N(t) = (1 + o(1)) √t e^{t/2}` and
  `N(t′)/N(t) = e^{(t′−t)/2} √(t′/t) (1 + o(1))`, with `o(1)` as `t → ∞` uniformly in `t′ ≥ t`
  (Corollary 2).
-/

open Finset Real Filter Topology Asymptotics

@[expose] public section

namespace CpsLean

/-! ### Theorem 1(i) -/

theorem tendsto_mul_step (hP : PNT) : Tendsto (fun m : ℕ => (m : ℝ) * step m) atTop (𝓝 2) := by
  have h := (LeanBase.PrimeSums.r_asymp (pntcons_of_PNT hP)).2
  -- `step (k+1)` is the step of lean-base at index `k`
  have hs : ∀ k : ℕ, step (k + 1) = log (LeanBase.PrimeSums.S (LeanBase.PrimeSums.p (k + 1))) -
      log (LeanBase.PrimeSums.S (LeanBase.PrimeSums.p k)) := by
    intro k
    simp only [step, sigma, prime_succ, S_eq_leanBase]
  have hk : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
    simp only [inv_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
  have h2 := h.mul hk
  rw [mul_one] at h2
  have h3 : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * step (k + 1)) atTop (𝓝 2) := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have : (0 : ℝ) < k := by exact_mod_cast hk
    rw [hs]; push_cast; field_simp
  exact (tendsto_add_atTop_iff_nat 1).1 h3

/-- **Theorem 1(i)** (Step Theorem). `Δ_m ∼ 2/m`. -/
theorem theorem1_i (hP : PNT) : step ~[atTop] (fun m : ℕ => 2 / (m : ℝ)) := by
  refine isEquivalent_of_tendsto_one ?_
  have := (tendsto_mul_step hP).div_const 2
  rw [div_self (two_ne_zero)] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Pi.div_apply]; field_simp

/-! ### The cell along `t → ∞` -/

theorem sigma_le_of_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : sigma m ≤ sigma n := by
  rcases hmn.lt_or_eq with h | rfl
  · exact (def1_sigma.1 m n hm h).le
  · exact le_rfl

theorem tendsto_cellIndex : Tendsto cellIndex atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [eventually_gt_atTop (max (log 3) (sigma (M + 1)))] with t ht
  have h3 : log 3 < t := lt_of_le_of_lt (le_max_left _ _) ht
  obtain ⟨hm2, -, -, hhi⟩ := cell_bracket h3
  by_contra h
  push Not at h
  have := sigma_le_of_le (by omega) (show cellIndex t ≤ M + 1 by omega)
  have : t < t := lt_of_le_of_lt hhi (this.trans_lt (lt_of_le_of_lt (le_max_right _ _) ht))
  exact lt_irrefl _ this

theorem cell_eq_step {t : ℝ} (ht : log 3 < t) : cell t = step (cellIndex t - 1) := by
  have := (cell_bracket ht).1
  rw [cell, step, show cellIndex t - 1 + 1 = cellIndex t by omega]

/-- `m(t) δ(t) → 2`. -/
theorem tendsto_cellIndex_mul_cell (hP : PNT) :
    Tendsto (fun t => (cellIndex t : ℝ) * cell t) atTop (𝓝 2) := by
  have hm1 : Tendsto (fun t => cellIndex t - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp tendsto_cellIndex
  have h := (tendsto_mul_step hP).comp hm1
  have hr : Tendsto (fun t => (cellIndex t : ℝ) / ((cellIndex t - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
    simp only [inv_one] at this
    refine (this.comp hm1).congr' ?_
    filter_upwards [tendsto_cellIndex.eventually_ge_atTop 2] with t ht
    have : (2 : ℝ) ≤ cellIndex t := by exact_mod_cast ht
    simp only [Function.comp_apply]
    rw [Nat.cast_sub (by omega)]; push_cast
    field_simp; ring
  have := h.mul hr
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop (log 3), tendsto_cellIndex.eventually_ge_atTop 2] with t ht ht2
  have : (2 : ℝ) ≤ cellIndex t := by exact_mod_cast ht2
  simp only [Function.comp_apply]
  rw [cell_eq_step ht, Nat.cast_sub (by omega)]; push_cast
  have hne : (cellIndex t : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem tendsto_cell_zero (hP : PNT) : Tendsto cell atTop (𝓝 0) := by
  have h := (tendsto_cellIndex_mul_cell hP).div_atTop
    (tendsto_natCast_atTop_atTop.comp tendsto_cellIndex)
  refine h.congr' ?_
  filter_upwards [tendsto_cellIndex.eventually_ge_atTop 1] with t ht
  have : (1 : ℝ) ≤ cellIndex t := by exact_mod_cast ht
  simp only [Function.comp_apply]; field_simp

theorem tendsto_eps_zero (hP : PNT) : Tendsto eps atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_cell_zero hP) ?_ ?_
  · filter_upwards [eventually_gt_atTop (log 3)] with t ht using (theorem2_d ht).1
  · filter_upwards [eventually_gt_atTop (log 3)] with t ht using (theorem2_d ht).2.1.le

theorem tendsto_firstCrossing : Tendsto (fun t => (firstCrossing t : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 fun M => ?_)
  filter_upwards [tendsto_cellIndex.eventually_ge_atTop (M + 1)] with t ht
  have : cellIndex t ≤ firstCrossing t + 1 := by
    unfold cellIndex Nat.primeCounting Nat.primeCounting'; exact Nat.count_le _
  omega

/-! ### Proposition 2 -/

/-- The quantity `2 log N − log log N − log 2`. -/
noncomputable def scale (N : ℝ) : ℝ := 2 * log N - log (log N) - log 2

/-- `log S_N − (2 log N − log log N − log 2) → 0`, from `S_N ∼ N²/(2 log N)`. -/
theorem tendsto_log_S_sub_scale (hP : PNT) :
    Tendsto (fun t => log (S (firstCrossing t)) - scale (firstCrossing t)) atTop (𝓝 0) := by
  have hN : Tendsto firstCrossing atTop atTop :=
    tendsto_natCast_atTop_iff.1 tendsto_firstCrossing
  have hS := (S_isEquivalent hP).comp_tendsto hN
  have hr := (isEquivalent_iff_tendsto_one (by
    filter_upwards [hN.eventually_ge_atTop 2] with t ht
    have : (2 : ℝ) ≤ firstCrossing t := by exact_mod_cast ht
    have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
    simp only [Function.comp_apply]; positivity)).1 hS
  have hlog := ((continuousAt_log one_ne_zero).tendsto.comp hr)
  rw [log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [hN.eventually_ge_atTop 2] with t ht
  have h2 : (2 : ℝ) ≤ firstCrossing t := by exact_mod_cast ht
  have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
  have hS0 := S_pos_real (firstCrossing t)
  simp only [Function.comp_apply, Pi.div_apply, scale]
  rw [log_div hS0.ne' (by positivity), log_div (by positivity) (by positivity), log_mul two_ne_zero
    hl.ne', log_pow]
  push_cast; ring

/-- **Proposition 2** (Scaling law). Along the first-crossing primes,
`t = 2 log N − log log N − log 2 + o(1)`, `N = N(t)`. -/
theorem prop2_scaling (hP : PNT) :
    Tendsto (fun t => t - (2 * log (firstCrossing t : ℝ) - log (log (firstCrossing t : ℝ)) - log 2))
      atTop (𝓝 0) := by
  have h := (tendsto_log_S_sub_scale hP).sub (tendsto_eps_zero hP)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards with t
  simp only [eps, scale]; ring

/-! ### Corollary 2 and Theorem 1(ii) -/

/-- `2 log N(t) / t → 1`. -/
theorem tendsto_two_log_div (hP : PNT) :
    Tendsto (fun t => 2 * log (firstCrossing t : ℝ) / t) atTop (𝓝 1) := by
  have hL : Tendsto (fun t => log (firstCrossing t : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_firstCrossing
  -- `log log N / log N → 0`
  have hll : Tendsto (fun t => log (log (firstCrossing t : ℝ)) / log (firstCrossing t : ℝ))
      atTop (𝓝 0) := by
    have := isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact this.comp hL
  -- `t / log N → 2`
  have h2 := prop2_scaling hP
  have hq : Tendsto (fun t => t / log (firstCrossing t : ℝ)) atTop (𝓝 2) := by
    have e1 := (h2.div_atTop hL)
    have e2 := (tendsto_const_nhds (x := log 2)).div_atTop hL
    have := ((e1.sub hll).sub e2).const_add 2
    simp only [sub_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with t ht
    field_simp; ring
  have := (hq.inv₀ two_ne_zero).const_mul 2
  rw [show (2 : ℝ) * 2⁻¹ = 1 by norm_num] at this
  refine this.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0, eventually_gt_atTop 0] with t ht ht0
  field_simp

/-- `N(t) / (√(2 log N(t)) e^{t/2}) → 1`. -/
theorem tendsto_N_div_aux (hP : PNT) :
    Tendsto (fun t => (firstCrossing t : ℝ) / (√(2 * log (firstCrossing t : ℝ)) * exp (t / 2)))
      atTop (𝓝 1) := by
  have h0 := (prop2_scaling hP).div_const (-2)
  rw [zero_div] at h0
  have h := (continuous_exp.tendsto 0).comp h0
  rw [Real.exp_zero] at h
  refine h.congr' ?_
  filter_upwards [tendsto_firstCrossing.eventually_ge_atTop 2] with t ht
  have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
  have hN : (0 : ℝ) < firstCrossing t := by linarith
  have hsq : √(2 * log (firstCrossing t : ℝ)) = exp (log (2 * log (firstCrossing t : ℝ)) / 2) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos (by positivity)]; ring_nf
  simp only [Function.comp_apply]
  rw [hsq, ← exp_add, eq_div_iff (exp_pos _).ne', ← exp_add]
  conv_rhs => rw [← exp_log hN]
  congr 1
  rw [log_mul two_ne_zero hl.ne']; ring

/-- **Corollary 2, first part.** `N(t) = (1 + o(1)) √t e^{t/2}`. -/
theorem firstCrossing_isEquivalent (hP : PNT) :
    (fun t => (firstCrossing t : ℝ)) ~[atTop] (fun t => √t * exp (t / 2)) := by
  refine isEquivalent_of_tendsto_one ?_
  have hs := (tendsto_two_log_div hP).sqrt
  rw [sqrt_one] at hs
  have := (tendsto_N_div_aux hP).mul hs
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [tendsto_firstCrossing.eventually_ge_atTop 2, eventually_gt_atTop 0] with t ht ht0
  have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
  simp only [Pi.div_apply]
  rw [sqrt_div' _ ht0.le]
  have : 0 < √(2 * log (firstCrossing t : ℝ)) := sqrt_pos.2 (by positivity)
  have : 0 < √t := sqrt_pos.2 ht0
  field_simp

/-- **Theorem 1(ii)** (Step Theorem), and the asymptotics of Theorem 2:
`δ(t) = (1 + o(1)) √t e^{−t/2}`. -/
theorem theorem1_ii (hP : PNT) : cell ~[atTop] (fun t => √t * exp (-(t / 2))) := by
  refine isEquivalent_of_tendsto_one ?_
  -- `m(t) = π(N(t)) ∼ N/log N`
  have hπ := hP.comp_tendsto tendsto_firstCrossing
  have hπr := (isEquivalent_iff_tendsto_one (by
    filter_upwards [tendsto_firstCrossing.eventually_ge_atTop 2] with t ht
    have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
    simp only [Function.comp_apply]; exact (div_pos (by linarith) hl).ne')).1 hπ
  have hc := (tendsto_cellIndex_mul_cell hP).div_const 2
  have hN := (firstCrossing_isEquivalent hP)
  have hNr := (isEquivalent_iff_tendsto_one (by
    filter_upwards [tendsto_firstCrossing.eventually_ge_atTop 2] with t ht
    exact (show (0 : ℝ) < firstCrossing t by linarith).ne')).1 hN.symm
  have := ((hc.mul (hπr.inv₀ one_ne_zero)).mul (tendsto_two_log_div hP)).mul hNr
  simp only [div_self (two_ne_zero' ℝ), inv_one, mul_one] at this
  refine this.congr' ?_
  filter_upwards [tendsto_firstCrossing.eventually_ge_atTop 2, eventually_gt_atTop (log 3),
    eventually_gt_atTop 0] with t ht ht3 ht0
  have hl : 0 < log (firstCrossing t : ℝ) := log_pos (by linarith)
  have hN0 : (0 : ℝ) < firstCrossing t := by linarith
  have hm : (cellIndex t : ℝ) = Nat.primeCounting ⌊(firstCrossing t : ℝ)⌋₊ := by
    rw [Nat.floor_natCast]; rfl
  have hm0 : (0 : ℝ) < cellIndex t := by
    have := (cell_bracket ht3).1; exact_mod_cast (show 0 < cellIndex t by omega)
  simp only [Function.comp_apply, Pi.div_apply, Pi.inv_apply, Pi.mul_apply, Nat.floor_natCast]
  have hm' : (Nat.primeCounting (firstCrossing t) : ℝ) = cellIndex t := rfl
  rw [hm']
  have hs0 : 0 < √t := sqrt_pos.2 ht0
  have hst : t = √t * √t := (mul_self_sqrt ht0.le).symm
  rw [exp_neg]
  generalize √t = s at hs0 hst ⊢
  subst hst
  simp only [← sq] at hm0 hN0 hl ⊢
  field_simp

/-- **Theorem 2, asymptotic part.** `δ(t) = (1 + o(1)) √t e^{−t/2}`; a restatement of Theorem 1(ii). -/
theorem theorem2_asymp (hP : PNT) : cell ~[atTop] (fun t => √t * exp (-(t / 2))) :=
  theorem1_ii hP

/-- **Corollary 2** (Half-exponent law, corrected form). `N(t) = (1 + o(1)) √t e^{t/2}`, hence
`N(t′)/N(t) = e^{(t′−t)/2} √(t′/t) (1 + o(1))`, with `o(1)` as `t → ∞` uniformly in `t′ ≥ t`. -/
theorem cor2_halfExponent (hP : PNT) :
    ((fun t => (firstCrossing t : ℝ)) ~[atTop] (fun t => √t * exp (t / 2))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t t' : ℝ, T ≤ t → t ≤ t' →
        |(firstCrossing t' : ℝ) / firstCrossing t / (exp ((t' - t) / 2) * √(t' / t)) - 1| < ε := by
  refine ⟨firstCrossing_isEquivalent hP, fun ε hε => ?_⟩
  have hN := (isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (mul_pos (sqrt_pos.2 ht) (exp_pos _)).ne')).1 (firstCrossing_isEquivalent hP)
  -- the ratio `r(t) = N(t) / (√t e^{t/2})` is within `η` of `1`
  set η := min (1 / 2) (ε / 4) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hN.eventually (Metric.ball_mem_nhds 1 hη0))
  refine ⟨max T 1, fun t t' ht htt' => ?_⟩
  have ht0 : 0 < t := by linarith [le_max_right T 1]
  have ht'0 : 0 < t' := by linarith
  have h1 := hT t (le_trans (le_max_left _ _) ht)
  have h2 := hT t' (le_trans (le_trans (le_max_left _ _) ht) htt')
  simp only [Pi.div_apply, Metric.mem_ball, Real.dist_eq] at h1 h2
  set r := (firstCrossing t : ℝ) / (√t * exp (t / 2))
  set r' := (firstCrossing t' : ℝ) / (√t' * exp (t' / 2))
  have hr : 1 / 2 ≤ r := by rw [abs_lt] at h1; linarith [min_le_left (1 / 2 : ℝ) (ε / 4)]
  have hq : (firstCrossing t' : ℝ) / firstCrossing t / (exp ((t' - t) / 2) * √(t' / t)) = r' / r := by
    have : 0 < √t := sqrt_pos.2 ht0
    have : 0 < √t' := sqrt_pos.2 ht'0
    have hN0 : (0 : ℝ) < firstCrossing t := by
      by_contra h
      push Not at h
      have : r ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
      linarith
    simp only [r, r']
    rw [sqrt_div' _ ht0.le, show (t' - t) / 2 = t' / 2 - t / 2 by ring, exp_sub]
    field_simp
  rw [hq, div_sub_one (by linarith), abs_div, abs_of_pos (show (0 : ℝ) < r by linarith)]
  rw [div_lt_iff₀ (by linarith)]
  have : |r' - r| < 2 * η := by
    calc |r' - r| = |(r' - 1) - (r - 1)| := by ring_nf
      _ ≤ |r' - 1| + |r - 1| := abs_sub _ _
      _ < η + η := add_lt_add h2 h1
      _ = 2 * η := by ring
  have : 2 * η ≤ ε / 2 := by linarith [min_le_right (1 / 2 : ℝ) (ε / 4)]
  nlinarith

end CpsLean
