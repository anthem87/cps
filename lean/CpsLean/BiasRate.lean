module

public import CpsLean.LocalLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
set_option autoImplicit false

/-!
# Theorem 4(b): the rate at which the bias fades

Put `A = a + ½`, `b_a = 1/(2a+1) = 1/(2A)`, `σ = σ_a`, `h_a = b_a/σ`. The law `μ_a` is symmetric about the
shift `b′ = −b_a = −1/(2A)`, so `W = (X_a − b′)/σ` is symmetric and `δ_a = P(X_a > 0) = P(W > h_a)`.

* `half_sub_deltaA_eq`: `½ − δ_a = P(0 < W ≤ h_a)`.
* `half_sub_deltaA_eq_sinc`: `½ − δ_a = (h_a/π) ∫_0^∞ sinc(h_a s) P_a(s/σ) ds`.
* `tendsto_half_sub_deltaA_div`: `(½ − δ_a)/h_a → (2π)^{−1/2}`, from Lemma W.
* `theorem4_b`: **Theorem 4(b)**, in analytic form (on the formula `deltaA`).
* `theorem4_b_density`: **Theorem 4(b)**, on the logarithmic density of the race.
-/

open Real Filter Topology MeasureTheory Set ProbabilityTheory Asymptotics

@[expose] public section

namespace CpsLean

/-- `½ − δ_a = P(0 < W ≤ h_a)`, where `W = (X_a − b′)/σ_a`, `X_a` has law `μ`, `b′ = −1/(2a+1)` is the
centre of `μ`, and `h_a = (1/(2a+1))/σ_a`. -/
theorem half_sub_deltaA_eq (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI)
    {a : ℝ} (ha : -1 / 2 < a) {μ : ProbabilityMeasure ℝ}
    (hμ : HasLimitingDistribution (phiA a) μ) :
    1 / 2 - deltaA a =
      ((μ : Measure ℝ).map fun t => (t - (-1 / (2 * a + 1))) / √(sigmaSq a)).real
        (Ioc 0 ((1 / (2 * a + 1)) / √(sigmaSq a))) := by
  have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr (sigmaSq_pos hN hRH a)
  have h21 : 0 < 2 * a + 1 := by linarith
  set σ := √(sigmaSq a) with hσ
  set b := 1 / (2 * a + 1) with hb
  have hb0 : 0 < b := by positivity
  have hneg : -1 / (2 * a + 1) = -b := by
    rw [hb]
    ring
  have hν := real_singleton_zero_and hRS (symm_shiftLaw hE hN hK h19 hRH hLI ha hμ)
    (integrable_charFun_shiftLaw hE hN hK h19 hB hRH hLI ha hμ)
  have h1 := real_Ioc_eq (ν := shiftLaw μ b) hb0.le
  rw [hν.2, real_shiftLaw_Ioi, deltaA_eq hE hN hK h19 hB hRS hRH hLI ha hμ] at h1
  rw [← h1, hneg, coe_shiftLaw, map_measureReal_apply (by fun_prop) measurableSet_Ioc,
    map_measureReal_apply (by fun_prop) measurableSet_Ioc]
  congr 1
  ext t
  simp only [mem_preimage, mem_Ioc, sub_neg_eq_add]
  rw [div_pos_iff_of_pos_right hσ0, div_le_div_iff_of_pos_right hσ0]

/-- `½ − δ_a = (h_a/π) ∫_0^∞ sinc(h_a s) P_a(s/σ) ds`. -/
theorem half_sub_deltaA_eq_sinc (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) {a : ℝ}
    (hA : 0 < a + 1 / 2) :
    1 / 2 - deltaA a = ((1 / (2 * a + 1)) / √(sigmaSq a)) / π *
      ∫ s in Ioi (0 : ℝ), sinc (((1 / (2 * a + 1)) / √(sigmaSq a)) * s) * prodJ a (s / √(sigmaSq a)) := by
  have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr (sigmaSq_pos hN hRH a)
  have h21 : 0 < 2 * a + 1 := by linarith
  set σ := √(sigmaSq a) with hσ
  set h := (1 / (2 * a + 1)) / σ with hh
  have hh0 : 0 < h := by positivity
  have hs := integral_comp_mul_left_Ioi (fun ξ : ℝ => sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ) 0
    (inv_pos.mpr hσ0)
  rw [mul_zero, inv_inv, smul_eq_mul] at hs
  have hpt : ∫ s in Ioi (0 : ℝ), sin (σ⁻¹ * s / (2 * a + 1)) / (σ⁻¹ * s) * prodJ a (σ⁻¹ * s) =
      (σ * h) * ∫ s in Ioi (0 : ℝ), sinc (h * s) * prodJ a (s / σ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs0 => ?_
    have hs1 : (0 : ℝ) < s := hs0
    have e1 : σ⁻¹ * s / (2 * a + 1) = h * s := by
      rw [hh]
      field_simp
    have e2 : σ⁻¹ * s = s / σ := by
      field_simp
    rw [e1, sinc_of_ne_zero (by positivity), e2]
    field_simp
  rw [hpt] at hs
  unfold deltaA
  have hI : ∫ ξ in Ioi (0 : ℝ), sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ =
      h * ∫ s in Ioi (0 : ℝ), sinc (h * s) * prodJ a (s / σ) := by
    have hne := hσ0.ne'
    have : σ * ∫ ξ in Ioi (0 : ℝ), sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ =
        σ * (h * ∫ s in Ioi (0 : ℝ), sinc (h * s) * prodJ a (s / σ)) := by
      rw [← hs]
      ring
    exact mul_left_cancel₀ hne this
  rw [hI]
  ring

/-- `(½ − δ_a)/h_a → (2π)^{−1/2}`. -/
theorem tendsto_half_sub_deltaA_div (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI)
    (hB : BesselDecay) :
    Tendsto (fun a : ℝ => (1 / 2 - deltaA a) / ((1 / (2 * a + 1)) / √(sigmaSq a))) atTop
      (𝓝 (√(2 * π))⁻¹) := by
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  set h : ℝ → ℝ := fun a => (1 / (2 * a + 1)) / √(sigmaSq a) with hh
  have hh0 : Tendsto h atTop (𝓝 0) := by
    have := ((tendsto_A_mul_sigma hN hRH hLI).const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).inv_tendsto_atTop
    refine this.congr fun a => ?_
    simp only [Pi.inv_apply, hh]
    rw [div_div, one_div]
    ring
  have hgm : ∀ a : ℝ, Measurable fun s : ℝ => sinc (h a * s) := fun a =>
    (continuous_sinc.comp (by fun_prop)).measurable
  -- the Gaussian part
  have hD2 : Tendsto (fun a : ℝ => ∫ s in Ioi (0 : ℝ), sinc (h a * s) * exp (-(s ^ 2 / 2))) atTop
      (𝓝 (∫ s in Ioi (0 : ℝ), exp (-(s ^ 2 / 2)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s : ℝ => exp (-(s ^ 2 / 2)))
      (Eventually.of_forall fun a => ((hgm a).mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun a => ae_of_all _ fun s => ?_)
      integrable_gauss.integrableOn (ae_of_all _ fun s => ?_)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_of_le_one_left (exp_pos _).le (abs_sinc_le_one _)
    · have h1 : Tendsto (fun a : ℝ => h a * s) atTop (𝓝 0) := by
        simpa using hh0.mul_const s
      have h2 := (continuous_sinc.tendsto 0).comp h1
      rw [sinc_zero] at h2
      simpa using h2.mul_const (exp (-(s ^ 2 / 2)))
  -- the difference
  have hD1 : Tendsto (fun a : ℝ => ∫ s in Ioi (0 : ℝ),
      sinc (h a * s) * (prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun a => ?_) (lemmaW hN hRH hLI hB)
    have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr (sigmaSq_pos hN hRH a)
    have hP := (integrable_prodJ hN hRH hB a).comp_div hσ0.ne'
    refine norm_integral_le_of_norm_le (hP.sub integrable_gauss).abs.integrableOn
      (ae_of_all _ fun s => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_sinc_le_one _)
  have hsum := (hD1.add hD2).const_mul (1 / π)
  rw [zero_add, integral_gauss_Ioi] at hsum
  have hval : 1 / π * (√(2 * π) / 2) = (√(2 * π))⁻¹ := by
    have hpi := pi_pos
    have hr : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have hrr : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    generalize √(2 * π) = r at hr hrr ⊢
    field_simp
    linarith
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [hAt.eventually_gt_atTop 0] with a ha
  have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr (sigmaSq_pos hN hRH a)
  have h21 : 0 < 2 * a + 1 := by linarith
  have hb : 0 < h a := by
    simp only [hh]
    positivity
  have hP := (integrable_prodJ hN hRH hB a).comp_div hσ0.ne'
  have hbd : ∀ {f : ℝ → ℝ}, Integrable f → Integrable fun s : ℝ => sinc (h a * s) * f s := fun hf =>
    hf.bdd_mul (c := 1) (hgm a).aestronglyMeasurable (ae_of_all _ fun s => by
      simpa using abs_sinc_le_one (h a * s))
  have e3 : 1 / 2 - deltaA a = h a / π *
      ∫ s in Ioi (0 : ℝ), sinc (h a * s) * prodJ a (s / √(sigmaSq a)) :=
    half_sub_deltaA_eq_sinc hN hRH ha
  have hi1 : Integrable fun s : ℝ =>
      sinc (h a * s) * (prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))) :=
    hbd (hP.sub integrable_gauss)
  have hi2 : Integrable fun s : ℝ => sinc (h a * s) * exp (-(s ^ 2 / 2)) := hbd integrable_gauss
  change _ = (1 / 2 - deltaA a) / h a
  rw [e3, ← integral_add hi1.integrableOn hi2.integrableOn]
  have e : ∫ s in Ioi (0 : ℝ), (sinc (h a * s) * (prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))) +
      sinc (h a * s) * exp (-(s ^ 2 / 2))) =
      ∫ s in Ioi (0 : ℝ), sinc (h a * s) * prodJ a (s / √(sigmaSq a)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  rw [e]
  have hne := hb.ne'
  generalize (∫ s in Ioi (0 : ℝ), sinc (h a * s) * prodJ a (s / √(sigmaSq a))) = J
  generalize h a = q at hne ⊢
  field_simp

/-- **Theorem 4(b).** Assume RH and LI, and put `A = a + ½`. Then
`½ − δ_a ∼ b_a/(σ_a √(2π))` with `b_a = 1/(2a+1)`, and `½ − δ_a ∼ 1/(2 √(π A log(A/2π)))`,
as `a → ∞`. -/
theorem theorem4_b (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) (hB : BesselDecay) :
    ((fun a : ℝ => 1 / 2 - deltaA a) ~[atTop]
      fun a : ℝ => (1 / (2 * a + 1)) / (√(sigmaSq a) * √(2 * π))) ∧
    ((fun a : ℝ => 1 / 2 - deltaA a) ~[atTop]
      fun a : ℝ => 1 / (2 * √(π * (a + 1 / 2) * log ((a + 1 / 2) / (2 * π))))) := by
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hLt : Tendsto (fun a : ℝ => log ((a + 1 / 2) / (2 * π))) atTop atTop :=
    tendsto_log_atTop.comp (hAt.atTop_div_const (by positivity))
  have hpi := pi_pos
  have hr : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hrr : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have h1 : (fun a : ℝ => 1 / 2 - deltaA a) ~[atTop]
      fun a : ℝ => (1 / (2 * a + 1)) / (√(sigmaSq a) * √(2 * π)) := by
    refine isEquivalent_of_tendsto_one ?_
    have hlim := (tendsto_half_sub_deltaA_div hN hRH hLI hB).mul_const (√(2 * π))
    rw [inv_mul_cancel₀ hr.ne'] at hlim
    refine hlim.congr' ?_
    filter_upwards [hAt.eventually_gt_atTop 0] with a ha
    have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr (sigmaSq_pos hN hRH a)
    have h21 : 0 < 2 * a + 1 := by linarith
    simp only [Pi.div_apply]
    field_simp
  refine ⟨h1, h1.trans ?_⟩
  -- the closed form
  have hw : ∀ᶠ a : ℝ in atTop, log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2)) ≠ 0 := by
    filter_upwards [hAt.eventually_gt_atTop 0, hLt.eventually_gt_atTop 0] with a ha hL
    positivity
  have hS := (isEquivalent_iff_tendsto_one hw).mp (sigmaSq_isEquivalent hN hRH hLI)
  have hinv := hS.inv₀ one_ne_zero
  rw [inv_one] at hinv
  have hsq := (continuous_sqrt.tendsto 1).comp hinv
  rw [Real.sqrt_one] at hsq
  refine isEquivalent_of_tendsto_one (hsq.congr' ?_)
  filter_upwards [hAt.eventually_gt_atTop 0, hLt.eventually_gt_atTop 0] with a ha hL
  have hsp := sigmaSq_pos hN hRH a
  have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr hsp
  have hσ2 : √(sigmaSq a) ^ 2 = sigmaSq a := Real.sq_sqrt hsp.le
  simp only [Function.comp_apply, Pi.div_apply]
  set A := a + 1 / 2 with hA
  set L := log (A / (2 * π)) with hLdef
  have e21 : 2 * a + 1 = 2 * A := by
    rw [hA]
    ring
  have hρ : 0 < √(π * A * L) := Real.sqrt_pos.mpr (by positivity)
  have hρ2 : √(π * A * L) ^ 2 = π * A * L := Real.sq_sqrt (by positivity)
  rw [e21]
  have hx : 1 / (2 * A) / (√(sigmaSq a) * √(2 * π)) / (1 / (2 * √(π * A * L))) =
      √(π * A * L) / (A * √(sigmaSq a) * √(2 * π)) := by
    field_simp
  rw [hx, ← Real.sqrt_sq (show 0 ≤ √(π * A * L) / (A * √(sigmaSq a) * √(2 * π)) by positivity)]
  congr 1
  rw [div_pow, mul_pow, mul_pow, hρ2, hσ2, hrr]
  field_simp

/-- **Theorem 4(b), on the density.** Assume RH and LI. For every `a > −½` the set where the race
`θ_a` is ahead of `li(x^{a+1})` has a logarithmic density `δ a`, and
`½ − δ a ∼ 1/(2 √(π A log(A/2π)))` as `a → ∞`, with `A = a + ½`. -/
theorem theorem4_b_density (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hC : AnsCor13a) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI) :
    ∃ δ : ℝ → ℝ,
      (∀ a : ℝ, -1 / 2 < a → HasLogDensity {x : ℝ | li (x ^ (a + 1)) < thetaPow a x} (δ a)) ∧
      ((fun a : ℝ => 1 / 2 - δ a) ~[atTop]
        fun a : ℝ => 1 / (2 * √(π * (a + 1 / 2) * log ((a + 1 / 2) / (2 * π))))) := by
  refine ⟨deltaA, fun a ha => ?_, (theorem4_b hN hRH hLI hB).2⟩
  obtain ⟨μ, hμ⟩ := exists_limiting hE hN hK hC hRH ha
  exact (theorem3_ii hE hN hK h19 hB hRS hRH hLI ha hμ).2.2.2.2

end CpsLean
