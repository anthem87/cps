module

public import CpsLean.Asymp
public import CpsLean.Grid
public import CpsLean.Classical.PNT
public import Mathlib.NumberTheory.AbelSummation
set_option autoImplicit false

/-!
# Consequences of the prime number theorem

From the hypothesis `PNT` (`π(x) ∼ x / log x`):

* `sumPrimes_isEquivalent`: `Σ_{p ≤ x} p ∼ x² / (2 log x)` (Abel summation:
  `Σ_{p≤x} p = x π(x) − ∫_0^x π(t) dt`, with `integral_isEquivalent` and
  `integral_id_div_log_isEquivalent`);
* `S_isEquivalent`: `S_N ∼ N² / (2 log N)` along the integers;
* `tendsto_prime_succ_div`: `p_{m+1} / p_m → 1`;
* `pntcons_of_PNT`: the hypothesis `LeanBase.PrimeSums.PNTcons` of lean-base holds.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory

@[expose] public section

namespace CpsLean

/-- `Σ_{p ≤ x} p` for real `x`. -/
noncomputable def sumPrimes (x : ℝ) : ℝ := ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime, (p : ℝ)

/-- The indicator of the primes. -/
noncomputable def primeInd (k : ℕ) : ℝ := if k.Prime then 1 else 0

theorem Icc_zero_eq_range (n : ℕ) : Icc 0 n = range (n + 1) := by
  ext k; simp only [mem_Icc, mem_range]; omega

theorem sum_primeInd (n : ℕ) : ∑ k ∈ Icc 0 n, primeInd k = (Nat.primeCounting n : ℝ) := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range, primeInd]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Icc_zero_eq_range]

theorem monotone_primeCounting_floor : Monotone (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ)) :=
  fun _ _ h => by dsimp only; exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono h)

theorem primeCounting_floor_of_lt_two {t : ℝ} (ht : t < 2) : Nat.primeCounting ⌊t⌋₊ = 0 := by
  have : ⌊t⌋₊ ≤ 1 := by
    have := Nat.floor_lt' (n := 2) (by norm_num) |>.2 ht
    omega
  interval_cases h : ⌊t⌋₊ <;> decide

/-- **Abel summation**: `Σ_{p ≤ x} p = x π(x) − ∫_2^x π(t) dt` for `x ≥ 2`. -/
theorem sumPrimes_eq {x : ℝ} (hx : 2 ≤ x) :
    sumPrimes x = x * Nat.primeCounting ⌊x⌋₊ - ∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
  have h := sum_mul_eq_sub_integral_mul primeInd (f := fun t : ℝ => t) (b := x) (by linarith)
    (fun t _ => differentiableAt_id) (by simp)
  simp only [deriv_id'', one_mul, sum_primeInd] at h
  have hl : ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ) * primeInd k = sumPrimes x := by
    simp only [primeInd, mul_ite, mul_one, mul_zero, sumPrimes]; rw [sum_filter]
  rw [hl] at h
  rw [h]
  congr 1
  rw [← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals
      (monotone_primeCounting_floor.intervalIntegrable (a := 0) (b := 2))
      (monotone_primeCounting_floor.intervalIntegrable (a := 2) (b := x))]
  have h0 : ∫ t in (0 : ℝ)..2, (Nat.primeCounting ⌊t⌋₊ : ℝ) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ)) fun t ht => by
      simp [primeCounting_floor_of_lt_two ht.2]]
    simp
  rw [h0, zero_add]

/-- **`Σ_{p ≤ x} p ∼ x² / (2 log x)`**, from the prime number theorem. -/
theorem sumPrimes_isEquivalent (hP : PNT) :
    sumPrimes ~[atTop] (fun x => x ^ 2 / (2 * log x)) := by
  set F : ℝ → ℝ := fun x => x ^ 2 / (2 * log x)
  have hH := integral_id_div_log_isEquivalent
  -- `∫_2^x π(t) dt ∼ F`
  have hI : (fun x => ∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ)) ~[atTop] F := by
    refine (integral_isEquivalent (a := 2)
      (fun x _ => monotone_primeCounting_floor.intervalIntegrable)
      (fun x hx => intervalIntegrable_of_Ici continuousOn_id_div_log le_rfl hx)
      (fun t ht => div_nonneg (by linarith) (log_nonneg (by linarith))) hP
      (hH.tendsto_atTop_iff.2 tendsto_sq_div_two_log)).trans hH
  -- `x π(x) ∼ 2F`
  have hX : (fun x : ℝ => x * (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x => 2 * F x) := by
    refine ((IsEquivalent.refl (u := fun x : ℝ => x)).mul hP).congr_right ?_
    filter_upwards with x
    simp only [F, Pi.mul_apply]; ring
  have h1 : (fun x : ℝ => x * (Nat.primeCounting ⌊x⌋₊ : ℝ) - 2 * F x) =o[atTop] F :=
    hX.isLittleO.trans_isBigO ((isBigO_refl F atTop).const_mul_left 2)
  have h2 : (fun x => (∫ t in (2 : ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ)) - F x) =o[atTop] F :=
    hI.isLittleO
  refine IsLittleO.isEquivalent ((h1.sub h2).congr' ?_ EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop 2] with x hx
  simp only [Pi.sub_apply]
  rw [sumPrimes_eq hx]; ring

theorem S_eq_sumPrimes (N : ℕ) : (S N : ℝ) = 1 + sumPrimes N := by
  unfold S sumPrimes
  push_cast
  rw [Nat.floor_natCast]
  rw [Icc_zero_eq_range]

/-- **`S_N ∼ N² / (2 log N)`** along the integers, from the prime number theorem. -/
theorem S_isEquivalent (hP : PNT) :
    (fun N : ℕ => (S N : ℝ)) ~[atTop] (fun N : ℕ => (N : ℝ) ^ 2 / (2 * log N)) := by
  have hN := (sumPrimes_isEquivalent hP).comp_tendsto tendsto_natCast_atTop_atTop
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2 / (2 * log N)) :=
    isLittleO_const_left.2 (Or.inr (tendsto_abs_atTop_atTop.comp
      (tendsto_sq_div_two_log.comp tendsto_natCast_atTop_atTop)))
  have := (h1.add hN.isLittleO)
  refine IsLittleO.isEquivalent (this.congr' ?_ EventuallyEq.rfl)
  filter_upwards with N
  simp only [Pi.sub_apply, Function.comp_apply, S_eq_sumPrimes]; ring

/-- `π(p_m) = m + 1` in the indices of lean-base (`p 0 = 2`). -/
theorem primeCounting_p (m : ℕ) : Nat.primeCounting (LeanBase.PrimeSums.p m) = m + 1 := by
  unfold Nat.primeCounting Nat.primeCounting' LeanBase.PrimeSums.p
  rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]

theorem tendsto_p_atTop : Tendsto (fun m : ℕ => (LeanBase.PrimeSums.p m : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-- From the prime number theorem: `π((1+η)x) / π(x) → 1 + η`. -/
theorem tendsto_primeCounting_ratio (hP : PNT) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊(1 + η) * x⌋₊ : ℝ) / Nat.primeCounting ⌊x⌋₊)
      atTop (𝓝 (1 + η)) := by
  have hc : Tendsto (fun x : ℝ => (1 + η) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h1 := hP.comp_tendsto hc
  -- `log((1+η)x) ∼ log x`
  have hlog : (fun x : ℝ => log ((1 + η) * x)) ~[atTop] log := by
    refine IsLittleO.isEquivalent ?_
    have : (fun x : ℝ => log ((1 + η) * x) - log x) =ᶠ[atTop] fun _ => log (1 + η) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [log_mul (by linarith) hx.ne']; ring
    refine (isLittleO_const_left.2 (Or.inr ?_)).congr' this.symm EventuallyEq.rfl
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop
  have h2 : (fun x : ℝ => (Nat.primeCounting ⌊(1 + η) * x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => (1 + η) * (x / log x)) := by
    refine h1.trans ?_
    have := (IsEquivalent.refl (u := fun x : ℝ => (1 + η) * x)).div hlog
    refine this.congr_right ?_
    filter_upwards with x; simp only [Pi.div_apply]; ring
  have h3 := h2.div hP
  have h4 : Tendsto (fun x : ℝ => (1 + η) * (x / log x) / (x / log x)) atTop (𝓝 (1 + η)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have : x / log x ≠ 0 := (div_pos (by linarith) (log_pos hx)).ne'
    have hl := (log_pos hx).ne'
    field_simp
  exact h3.symm.tendsto_nhds h4 |>.congr' (by filter_upwards with x; rfl)

/-- **`p_{m+1} / p_m → 1`**, from the prime number theorem (indices of lean-base). -/
theorem tendsto_p_succ_div (hP : PNT) :
    Tendsto (fun m : ℕ => (LeanBase.PrimeSums.p (m + 1) : ℝ) / LeanBase.PrimeSums.p m) atTop (𝓝 1) := by
  have hpos : ∀ m, (0 : ℝ) < LeanBase.PrimeSums.p m := fun m => by
    exact_mod_cast (LeanBase.PrimeSums.p_prime m).pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 2 with hηdef
  have hη : 0 < η := by positivity
  have hr := (tendsto_primeCounting_ratio hP hη).comp tendsto_p_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hr.eventually (lt_mem_nhds (show (1 : ℝ) < 1 + η by linarith)))
  refine ⟨M, fun m hm => ?_⟩
  have hgt := hM m hm
  simp only [Function.comp_apply, Nat.floor_natCast, primeCounting_p] at hgt
  set n := ⌊(1 + η) * (LeanBase.PrimeSums.p m : ℝ)⌋₊
  have hcount : m + 1 < Nat.primeCounting n := by
    have h0 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    rw [lt_div_iff₀ (by push_cast; positivity)] at hgt
    have : ((m + 1 : ℕ) : ℝ) < Nat.primeCounting n := by push_cast at hgt ⊢; linarith
    exact_mod_cast this
  have hle : LeanBase.PrimeSums.p (m + 1) ≤ n := by
    have := Nat.nth_lt_of_lt_count
      (show m + 1 < Nat.count Nat.Prime (n + 1) by
        simpa [Nat.primeCounting, Nat.primeCounting'] using hcount)
    unfold LeanBase.PrimeSums.p; omega
  have hle' : (LeanBase.PrimeSums.p (m + 1) : ℝ) ≤ (1 + η) * LeanBase.PrimeSums.p m :=
    (Nat.cast_le.2 hle).trans (Nat.floor_le (by positivity))
  have hge : (LeanBase.PrimeSums.p m : ℝ) ≤ LeanBase.PrimeSums.p (m + 1) := by
    exact_mod_cast (LeanBase.PrimeSums.p_lt_succ m).le
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : 1 ≤ (LeanBase.PrimeSums.p (m + 1) : ℝ) / LeanBase.PrimeSums.p m := by
      rw [le_div_iff₀ (hpos m)]; linarith
    linarith
  · have : (LeanBase.PrimeSums.p (m + 1) : ℝ) / LeanBase.PrimeSums.p m ≤ 1 + η := by
      rw [div_le_iff₀ (hpos m)]; linarith
    linarith

/-- **The hypothesis `PNTcons` of lean-base follows from the prime number theorem.** -/
theorem pntcons_of_PNT (hP : PNT) : LeanBase.PrimeSums.PNTcons := by
  refine ⟨tendsto_p_succ_div hP, ?_⟩
  -- `S_{p_m} ∼ p_m² / (2 log p_m)` and `m + 1 = π(p_m) ∼ p_m / log p_m`
  have hS := (S_isEquivalent hP).comp_tendsto
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hπ := hP.comp_tendsto tendsto_p_atTop
  simp only [Function.comp_def, Nat.floor_natCast, primeCounting_p] at hS hπ
  have hq := hS.div (hπ.mul (IsEquivalent.refl (u := fun m : ℕ => (LeanBase.PrimeSums.p m : ℝ))))
  have hlim : Tendsto (fun m : ℕ => (LeanBase.PrimeSums.p m : ℝ) ^ 2 /
      (2 * log (LeanBase.PrimeSums.p m)) / ((LeanBase.PrimeSums.p m : ℝ) /
        log (LeanBase.PrimeSums.p m) * LeanBase.PrimeSums.p m)) atTop (𝓝 (1 / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with m
    have hp2 : (2 : ℝ) ≤ LeanBase.PrimeSums.p m := by exact_mod_cast (LeanBase.PrimeSums.p_prime m).two_le
    have hl : 0 < log (LeanBase.PrimeSums.p m : ℝ) := log_pos (by linarith)
    have : (0 : ℝ) < LeanBase.PrimeSums.p m := by linarith
    field_simp
  have h1 := hq.symm.tendsto_nhds hlim
  -- replace `m + 1` by `m`
  have hm : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ) / m) atTop (𝓝 1) := by
    have := tendsto_natCast_div_add_atTop (1 : ℝ)
    have h' := this.inv₀ one_ne_zero
    simp only [inv_one] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have : (0 : ℝ) < m := by exact_mod_cast hm
    push_cast; field_simp
  have := h1.mul hm
  simp only [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < LeanBase.PrimeSums.p m := by
    exact_mod_cast (LeanBase.PrimeSums.p_prime m).pos
  show _ = (LeanBase.PrimeSums.S (LeanBase.PrimeSums.p m) : ℝ) / (m * LeanBase.PrimeSums.p m)
  rw [← S_eq_leanBase]
  simp only [Pi.div_apply, Pi.mul_apply]
  push_cast
  change (S (LeanBase.PrimeSums.p m) : ℝ) / (((m : ℝ) + 1) * LeanBase.PrimeSums.p m) *
    (((m : ℝ) + 1) / m) = _
  field_simp

end CpsLean
