module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false

/-!
# `ζ` does not vanish on the real interval `(0, 1)`

`riemannZeta_ne_zero_of_real`: `ζ(σ) ≠ 0` for real `0 < σ < 1`. So, under the Riemann hypothesis,
no nontrivial zero has ordinate `0`, which Step 4 of Theorem 3 uses when it pairs the conjugate
zeros.

The proof is the alternating series: `F(s) = Σ_{n≥0} ((2n+1)^{−s} − (2n+2)^{−s})` is holomorphic on
`Re s > 0`, it equals `(1 − 2^{1−s}) ζ(s)` for `Re s > 1`, so on `Re s > 0` away from `1` by the
identity theorem, and `F(σ) > 0` for real `σ > 0`.
-/

open Complex Filter Topology Set

@[expose] public section

namespace CpsLean

/-- The `n`-th term `(2n+1)^{−s} − (2n+2)^{−s}` of the alternating series. -/
noncomputable def etaTerm (n : ℕ) (s : ℂ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℂ)) ^ (-s) - (((2 * n + 2 : ℕ) : ℂ)) ^ (-s)

/-- The alternating series. -/
noncomputable def etaF (s : ℂ) : ℂ := ∑' n, etaTerm n s

theorem norm_etaTerm_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖etaTerm n s‖ ≤ ‖s‖ * ((2 * n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  set a : ℝ := ((2 * n + 1 : ℕ) : ℝ) with ha
  set b : ℝ := ((2 * n + 2 : ℕ) : ℝ) with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : a ≤ b := by
    rw [ha, hb]
    push_cast
    linarith
  have hba : b - a = 1 := by
    rw [ha, hb]
    push_cast
    ring
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have h0 : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  have hr : -s - 1 ≠ -1 := by
    intro h
    apply hs0
    linear_combination -h
  have hint := integral_cpow (a := a) (b := b) (r := -s - 1) (Or.inr ⟨hr, h0⟩)
  rw [sub_add_cancel] at hint
  have hterm : etaTerm n s = s * ∫ t in a..b, (t : ℂ) ^ (-s - 1) := by
    rw [hint]
    unfold etaTerm
    have ca : (((2 * n + 1 : ℕ) : ℂ)) = (a : ℂ) := by rw [ha]; norm_cast
    have cb : (((2 * n + 2 : ℕ) : ℂ)) = (b : ℂ) := by rw [hb]; norm_cast
    rw [ca, cb]
    field_simp
    ring
  rw [hterm, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ∀ t ∈ Set.uIoc a b, ‖(t : ℂ) ^ (-s - 1)‖ ≤ a ^ (-s.re - 1) := by
    intro t ht
    rw [uIoc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    exact (Real.rpow_le_rpow_iff_of_neg ht0 ha0 (by linarith)).mpr ht.1.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (by linarith), hba, mul_one] at this
  exact this

theorem summable_two_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) ^ (-ε - 1)) := by
  have h : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-ε - 1)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  refine (Real.rpow_le_rpow_iff_of_neg (by positivity) (by positivity) (by linarith)).mpr ?_
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem differentiableAt_etaTerm (n : ℕ) (s : ℂ) : DifferentiableAt ℂ (etaTerm n) s := by
  unfold etaTerm
  have h1 : (((2 * n + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (((2 * n + 2 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
    (differentiableAt_id.neg.const_cpow (Or.inl h2))

theorem differentiableAt_etaF {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ etaF s := by
  set ε := s.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  set R := ‖s‖ + 1 with hR
  set D : Set ℂ := {z | ε < z.re} ∩ Metric.ball 0 R with hD
  have hDo : IsOpen D := (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hsD : s ∈ D := by
    refine ⟨?_, ?_⟩
    · change ε < s.re
      rw [hε]
      linarith
    · rw [mem_ball_zero_iff, hR]
      linarith
  have hF := Complex.differentiableOn_tsum_of_summable_norm (U := D) (F := etaTerm)
    (u := fun n => R * ((2 * n + 1 : ℕ) : ℝ) ^ (-ε - 1))
    ((summable_two_mul_rpow hε0).mul_left R)
    (fun n => fun z _ => (differentiableAt_etaTerm n z).differentiableWithinAt) hDo
    (fun n z hz => by
      have hz1 : ε < z.re := hz.1
      have hz2 : ‖z‖ < R := by simpa using hz.2
      refine (norm_etaTerm_le n (hε0.trans hz1)).trans ?_
      have hbase : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have : ((2 * n + 1 : ℕ) : ℝ) ^ (-z.re - 1) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      exact mul_le_mul hz2.le this (by positivity) (by positivity))
  exact (hF s hsD).differentiableAt (hDo.mem_nhds hsD)

/-- **`F(s) = (1 − 2^{1−s}) ζ(s)`** for `Re s > 1`. -/
theorem etaF_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    etaF s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hne : ∀ m : ℕ, ((m + 1 : ℕ) : ℂ) ≠ 0 := fun m => by exact_mod_cast Nat.succ_ne_zero m
  set f : ℕ → ℂ := fun m => ((m + 1 : ℕ) : ℂ) ^ (-s) with hf
  have hzeta : riemannZeta s = ∑' m, f m := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun m => ?_
    simp only [hf]
    rw [cpow_neg, one_div]
    push_cast
    rfl
  have hsum : Summable f := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    refine h.congr fun m => ?_
    simp only [hf]
    rw [cpow_neg, one_div]
  have he : Summable fun k => f (2 * k) :=
    hsum.comp_injective (fun x y h => by simpa using h)
  have ho : Summable fun k => f (2 * k + 1) :=
    hsum.comp_injective (fun x y h => by simpa using h)
  have heo := tsum_even_add_odd he ho
  have hodd : ∑' k, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [hzeta, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [hf]
    have : ((2 * k + 1 + 1 : ℕ) : ℂ) = (2 : ℂ) * ((k + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [this]
    have h := Complex.natCast_mul_natCast_cpow 2 (k + 1) (-s)
    simpa using h
  have hF : etaF s = ∑' k, f (2 * k) - ∑' k, f (2 * k + 1) := by
    unfold etaF
    rw [← he.tsum_sub ho]
    refine tsum_congr fun k => ?_
    simp only [etaTerm, hf]
  have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ (by norm_num), cpow_one]
  rw [hF, hpow]
  rw [← hzeta] at heo
  rw [hodd] at heo ⊢
  linear_combination heo

/-- **`ζ(σ) ≠ 0` for real `0 < σ < 1`.** -/
theorem riemannZeta_ne_zero_of_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  -- the two sides are holomorphic on `V₁` and `V₂`
  set G : ℂ → ℂ := fun s => (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s with hG
  have hGd : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ G s := fun s hs =>
    ((differentiableAt_const _).sub
      ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl (by norm_num)))).mul
      (differentiableAt_riemannZeta hs)
  set V₁ : Set ℂ := {z | 0 < z.re} ∩ {z | 0 < z.im} with hV₁
  set V₂ : Set ℂ := {z | 0 < z.re} ∩ {z | z.re < 1} with hV₂
  have hV₁o : IsOpen V₁ :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
  have hV₂o : IsOpen V₂ :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hV₁c : Convex ℝ V₁ :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hV₂c : Convex ℝ V₂ :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hne1 : ∀ z ∈ V₁, z ≠ 1 := fun z hz h => by
    have : 0 < z.im := hz.2
    rw [h] at this
    simp at this
  have hne2 : ∀ z ∈ V₂, z ≠ 1 := fun z hz h => by
    have : z.re < 1 := hz.2
    rw [h] at this
    simp at this
  have hF1 : AnalyticOnNhd ℂ etaF V₁ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_etaF hz.1).differentiableWithinAt) hV₁o
  have hG1 : AnalyticOnNhd ℂ G V₁ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hGd z (hne1 z hz)).differentiableWithinAt) hV₁o
  have hF2 : AnalyticOnNhd ℂ etaF V₂ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_etaF hz.1).differentiableWithinAt) hV₂o
  have hG2 : AnalyticOnNhd ℂ G V₂ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hGd z (hne2 z hz)).differentiableWithinAt) hV₂o
  -- from `Re s > 1` to `V₁`
  set z₀ : ℂ := 2 + I with hz₀
  have hz₀V : z₀ ∈ V₁ := by
    refine ⟨?_, ?_⟩ <;> simp [hz₀]
  have hev : etaF =ᶠ[𝓝 z₀] G := by
    have hop : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    have hm : z₀ ∈ {z : ℂ | 1 < z.re} := by simp [hz₀]
    filter_upwards [hop.mem_nhds hm] with z hz
    exact etaF_eq_of_one_lt hz
  have heq1 : EqOn etaF G V₁ :=
    hF1.eqOn_of_preconnected_of_eventuallyEq hG1 hV₁c.isPreconnected hz₀V hev
  -- from `V₁` to `V₂`
  set z₁ : ℂ := (1 / 2 : ℝ) + I with hz₁
  have hz₁1 : z₁ ∈ V₁ := by
    refine ⟨?_, ?_⟩ <;> simp [hz₁]
  have hz₁2 : z₁ ∈ V₂ := by
    refine ⟨?_, ?_⟩ <;> simp [hz₁]
    norm_num
  have hev2 : etaF =ᶠ[𝓝 z₁] G := by
    filter_upwards [hV₁o.mem_nhds hz₁1] with z hz
    exact heq1 hz
  have heq2 : EqOn etaF G V₂ :=
    hF2.eqOn_of_preconnected_of_eventuallyEq hG2 hV₂c.isPreconnected hz₁2 hev2
  have hσ : (σ : ℂ) ∈ V₂ := by
    refine ⟨?_, ?_⟩ <;> simpa
  have hval := heq2 hσ
  -- `F(σ) > 0`
  set g : ℕ → ℝ := fun n => ((2 * n + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * n + 2 : ℕ) : ℝ) ^ (-σ) with hg
  have hterm : ∀ n, etaTerm n (σ : ℂ) = (g n : ℂ) := by
    intro n
    unfold etaTerm
    simp only [hg]
    push_cast
    rw [ofReal_cpow (by positivity), ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hgpos : ∀ n, 0 < g n := by
    intro n
    simp only [hg]
    rw [sub_pos]
    refine (Real.rpow_lt_rpow_iff_of_neg (by positivity) (by positivity) (by linarith)).mpr ?_
    push_cast
    linarith
  have hgsum : Summable g := by
    have hb : Summable (fun n : ℕ => ‖(σ : ℂ)‖ * ((2 * n + 1 : ℕ) : ℝ) ^ (-σ - 1)) :=
      (summable_two_mul_rpow h0).mul_left _
    refine hb.of_nonneg_of_le (fun n => (hgpos n).le) fun n => ?_
    have := norm_etaTerm_le n (s := (σ : ℂ)) (by simpa)
    rw [hterm, norm_real, Real.norm_of_nonneg (hgpos n).le] at this
    simpa using this
  have hFpos : etaF (σ : ℂ) = ((∑' n, g n : ℝ) : ℂ) := by
    unfold etaF
    rw [ofReal_tsum]
    exact tsum_congr hterm
  have hne : etaF (σ : ℂ) ≠ 0 := by
    rw [hFpos]
    exact_mod_cast (hgsum.tsum_pos (fun n => (hgpos n).le) 0 (hgpos 0)).ne'
  intro hz
  apply hne
  rw [hval]
  simp only [hG, hz, mul_zero]

end CpsLean
