module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false

/-!
# The Bessel function `J₀` and Lemma J

`besselJ0 x = J₀(x) = Σ_{k≥0} (−1)^k (x/2)^{2k} / (k!)²`, the Bessel function of the first kind of
order `0` (it enters the densities of Theorem 3(ii)).

* `lemmaJ`: for `|x| ≤ 2`, `0 ≤ J₀(x) ≤ e^{−x²/4}`.

With `y = x²/4 ≤ 1` the series of `J₀(x)` and of `e^{−y}` are alternating with decreasing terms, so
their partial sums bound them: `1 − y ≤ J₀(x) ≤ 1 − y + y²/4` and
`e^{−y} ≥ 1 − y + y²/2 − y³/6 ≥ 1 − y + y²/4`.
-/

open Finset Real Filter Topology Nat

@[expose] public section

namespace CpsLean

/-- The Bessel function `J₀(x) = Σ_{k≥0} (−1)^k (x/2)^{2k} / (k!)²`. -/
noncomputable def besselJ0 (x : ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * (x / 2) ^ (2 * k) / ((k ! : ℝ) ^ 2)

/-- Partial sums of an alternating series with terms decreasing to `0`, from a `HasSum`. -/
theorem alternating_bounds {f : ℕ → ℝ} {l : ℝ} (hf : Antitone f)
    (hs : HasSum (fun i => (-1 : ℝ) ^ i * f i) l) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * f i ≤ l ∧ l ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * f i :=
  ⟨hf.alternating_series_le_tendsto hs.tendsto_sum_nat k,
    hf.tendsto_le_alternating_series hs.tendsto_sum_nat k⟩

theorem factorial_sq_pos (k : ℕ) : (0 : ℝ) < (k ! : ℝ) ^ 2 := by positivity

/-- The terms `y^k/(k!)²` of `J₀`, as a function of `y = x²/4`. -/
theorem besselJ0_hasSum (x : ℝ) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k * ((x ^ 2 / 4) ^ k / (k ! : ℝ) ^ 2)) (besselJ0 x) := by
  set y := x ^ 2 / 4
  have hterm : ∀ k : ℕ, (-1 : ℝ) ^ k * (x / 2) ^ (2 * k) / ((k ! : ℝ) ^ 2) =
      (-1 : ℝ) ^ k * (y ^ k / (k ! : ℝ) ^ 2) := by
    intro k; rw [pow_mul]; simp only [y]; ring
  have hsum : Summable (fun k : ℕ => (-1 : ℝ) ^ k * (y ^ k / (k ! : ℝ) ^ 2)) := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |y|) fun k => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, norm_pow,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (factorial_sq_pos k)]
    have h1 : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (factorial_ne_zero k)
    have h2 : (k ! : ℝ) ≤ (k ! : ℝ) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  have : besselJ0 x = ∑' k : ℕ, (-1 : ℝ) ^ k * (y ^ k / (k ! : ℝ) ^ 2) := by
    unfold besselJ0; exact tsum_congr hterm
  rw [this]; exact hsum.hasSum

theorem exp_neg_hasSum (y : ℝ) : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (y ^ k / k !)) (exp (-y)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-y)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  ext k; rw [neg_pow]; ring

/-- **Lemma J.** For `|x| ≤ 2`, `0 ≤ J₀(x) ≤ e^{−x²/4}`. -/
theorem lemmaJ {x : ℝ} (hx : |x| ≤ 2) : 0 ≤ besselJ0 x ∧ besselJ0 x ≤ exp (-(x ^ 2 / 4)) := by
  set y := x ^ 2 / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by
    have : x ^ 2 ≤ 4 := by nlinarith [abs_nonneg x, sq_abs x]
    simp only [y]; linarith
  -- the terms of `J₀` decrease
  have ha : Antitone (fun k : ℕ => y ^ k / (k ! : ℝ) ^ 2) := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [pow_succ, factorial_succ]; push_cast
    have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast factorial_pos k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hyk : 0 ≤ y ^ k := pow_nonneg hy0 k
    nlinarith [mul_le_mul_of_nonneg_left hy1 hyk, mul_nonneg hyk (sq_nonneg (k ! : ℝ))]
  -- the terms of `e^{−y}` decrease
  have hb : Antitone (fun k : ℕ => y ^ k / (k ! : ℝ)) := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [pow_succ, factorial_succ]; push_cast
    have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast factorial_pos k
    rw [div_le_div_iff₀ (by positivity) hk]
    have hyk : 0 ≤ y ^ k := pow_nonneg hy0 k
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith [mul_le_mul_of_nonneg_left hy1 hyk, mul_nonneg hyk hk.le]
  obtain ⟨hJlo, hJhi⟩ := alternating_bounds ha (besselJ0_hasSum x) 1
  obtain ⟨hElo, -⟩ := alternating_bounds hb (exp_neg_hasSum y) 2
  simp only [show 2 * 1 = 2 by rfl, show 2 * 1 + 1 = 3 by rfl, show 2 * 2 = 4 by rfl,
    sum_range_succ, sum_range_zero] at hJlo hJhi hElo
  norm_num [factorial] at hJlo hJhi hElo
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg (sq_nonneg y) (show (0 : ℝ) ≤ 1 / 4 - y / 6 by linarith)]

end CpsLean
