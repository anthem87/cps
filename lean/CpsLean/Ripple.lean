module

public import CpsLean.Grid
public import LeanBase.Classical.Prop30
set_option autoImplicit false

/-!
# The ripple and the Riemann hypothesis: Proposition 3(b) (Section 8.3 of the paper)

* `Sx x = S(x) = 1 + Σ_{p ≤ x} p` for real `x`, and `B x = B(x) = 1 + li(x²) − li(4)`, written as
  `1 + ∫_4^{x²} du / log u` (the same quantity, without the principal value at `0`).
* `S_sub_B_eq`: for `N ≥ 2`, `S(N) − B(N) = Σ_{p ≤ N} p − ∫_2^N t dt / log t`, which is
  `LeanBase.Classical.momentError 1 N`.
* `prop3b_ripple_imp_RH`: if `S(x) − B(x) = O(x^{3/2+ε})` for every `ε > 0`, the Riemann hypothesis
  holds. The proof is Landau's theorem as proved in `LeanBase.Classical.prop30_two_imp_RH`, which
  needs only the upper bound.
-/

open Finset Real Filter Asymptotics MeasureTheory

@[expose] public section

namespace CpsLean

/-- `S(x) = 1 + Σ_{p ≤ x} p` for real `x` (Section 8.1). -/
noncomputable def Sx (x : ℝ) : ℝ := S ⌊x⌋₊

/-- The mean curve `B(x) = 1 + li(x²) − li(4)` (Section 8.1), with `li(x²) − li(4) = ∫_4^{x²} du/log u`. -/
noncomputable def B (x : ℝ) : ℝ := 1 + ∫ u in (4 : ℝ)..x ^ 2, 1 / log u

/-- `∫_4^{x²} du / log u = ∫_2^x t dt / log t` for `x ≥ 2` (substitution `u = t²`). -/
theorem integral_inv_log_sq {x : ℝ} (hx : 2 ≤ x) :
    ∫ u in (4 : ℝ)..x ^ 2, 1 / log u = ∫ t in (2 : ℝ)..x, t / log t := by
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 2) (b := x)
    (f := fun t : ℝ => t ^ 2) (f' := fun t => 2 * t) (g := fun u => 1 / log u)
    (fun t _ => by simpa using hasDerivAt_pow 2 t)
    (by fun_prop)
    (by
      rintro u ⟨t, ht, rfl⟩
      rw [Set.uIcc_of_le hx] at ht
      have h4 : (4 : ℝ) ≤ t ^ 2 := by nlinarith [ht.1]
      have hpos : 0 < log (t ^ 2) := log_pos (by linarith)
      exact (continuousAt_const.div (continuousAt_log (by positivity)) hpos.ne').continuousWithinAt)
  simp only [Function.comp_def] at hsub
  rw [show ((2 : ℝ) ^ 2) = 4 by norm_num] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hl : 0 < log t := log_pos (by linarith [ht.1])
  rw [log_pow]; push_cast; field_simp

/-- `Li₁(x) = ∫_2^x t dt / log t` for `x ≥ 2`. -/
theorem liK_one_eq {x : ℝ} (hx : 2 ≤ x) :
    LeanBase.Classical.liK 1 x = ∫ t in (2 : ℝ)..x, t / log t := by
  unfold LeanBase.Classical.liK
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (LeanBase.Classical.intervalIntegrable_liIntegrand 1 0 2)
    (LeanBase.Classical.intervalIntegrable_liIntegrand 1 2 x)]
  have h0 : ∫ t in (0 : ℝ)..2, LeanBase.Classical.liIntegrand 1 t = 0 :=
    LeanBase.Classical.liK_of_le_two 1 le_rfl
  rw [h0, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Set.uIoc_of_le hx] at ht
  simp [LeanBase.Classical.liIntegrand, ht.1]

/-- `Σ_{p ≤ N} p = S_N − 1`, as the prime race with weight `p`. -/
theorem primeRace_one_eq (N : ℕ) :
    LeanBase.Classical.primeRace (LeanBase.Classical.powWeight 1) N = (S N : ℝ) - 1 := by
  rw [LeanBase.Classical.primeRace_natCast]
  unfold S
  push_cast
  rw [add_sub_cancel_left]
  simp only [LeanBase.Classical.primeCoeff, LeanBase.Classical.powWeight, pow_one]
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩

/-- For `N ≥ 2`, `S(N) − B(N) = E₁(N) = Σ_{p ≤ N} p − Li₁(N)`. -/
theorem S_sub_B_eq {N : ℕ} (hN : 2 ≤ N) :
    Sx N - B N = LeanBase.Classical.momentError 1 N := by
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Sx, Nat.floor_natCast, B, LeanBase.Classical.momentError, primeRace_one_eq,
    liK_one_eq hx, integral_inv_log_sq hx]
  ring

/-- **Proposition 3(b).** If `S(x) − B(x) = O(x^{3/2+ε})` for every `ε > 0`, then the Riemann
hypothesis holds. -/
theorem prop3b_ripple_imp_RH
    (h : ∀ ε : ℝ, 0 < ε → (fun x : ℝ => Sx x - B x) =O[atTop] (fun x : ℝ => x ^ ((3 : ℝ) / 2 + ε))) :
    RiemannHypothesis := by
  refine LeanBase.Classical.prop30_two_imp_RH 1 fun ε hε => ?_
  have hθ : ((1 : ℕ) : ℝ) + 1 / 2 + ε = 3 / 2 + ε := by push_cast; ring
  rw [hθ]
  obtain ⟨c, hc⟩ := (h ε hε).bound
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hc
  set C₁ : ℝ := ∑ n ∈ range ⌈x₀⌉₊, |LeanBase.Classical.momentError 1 (n : ℝ)|
  refine ⟨max c 0 + C₁, fun N hN => ?_⟩
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 + ε) := one_le_rpow hN0 (by linarith)
  have hC₁ : 0 ≤ C₁ := sum_nonneg fun _ _ => abs_nonneg _
  by_cases hN₀ : x₀ ≤ N
  · have hb := hx₀ N hN₀
    rw [S_sub_B_eq hN, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 2 + ε))] at hb
    calc LeanBase.Classical.momentError 1 N ≤ c * (N : ℝ) ^ ((3 : ℝ) / 2 + ε) :=
          (le_abs_self _).trans hb
      _ ≤ max c 0 * (N : ℝ) ^ ((3 : ℝ) / 2 + ε) := by gcongr; exact le_max_left _ _
      _ ≤ (max c 0 + C₁) * (N : ℝ) ^ ((3 : ℝ) / 2 + ε) := by gcongr; linarith
  · push Not at hN₀
    have hmem : N ∈ range ⌈x₀⌉₊ := by
      rw [mem_range]; exact Nat.lt_ceil.2 hN₀
    have h1 : LeanBase.Classical.momentError 1 N ≤ C₁ :=
      (le_abs_self _).trans (single_le_sum (f := fun n : ℕ => |LeanBase.Classical.momentError 1 (n : ℝ)|)
        (fun _ _ => abs_nonneg _) hmem)
    calc LeanBase.Classical.momentError 1 N ≤ C₁ := h1
      _ ≤ (max c 0 + C₁) * 1 := by linarith [le_max_right c 0]
      _ ≤ (max c 0 + C₁) * (N : ℝ) ^ ((3 : ℝ) / 2 + ε) := by
          gcongr

end CpsLean
