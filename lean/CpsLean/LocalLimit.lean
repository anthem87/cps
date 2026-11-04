module

public import CpsLean.BesselTheta
public import CpsLean.BiasFade
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
set_option autoImplicit false

/-!
# Lemma W: a local limit theorem for the symmetric part of `μ_a`

With `A = a + ½` and `σ = σ_a`, the characteristic function of the normalized symmetric part of `μ_a`
is `s ↦ P_a(s/σ)`, where `P_a = prodJ a`.

* `prodJ_central`: for `|ξ| ≤ A`, `0 ≤ P_a(ξ) ≤ e^{−ξ²σ²/2}` (Lemma J, factor by factor).
* `abs_prodJ_tail`: for `|ξ| ≥ A`, `|P_a(ξ)| ≤ θ^{K−4} C⁴ A²/(2ξ²)`, where `C` is the constant of
  `BesselDecay`, `θ = sup_{|u| ≥ √2} |J₀(u)| < 1`, and `K` zeros have `0 < γ ≤ A`.
* `lemmaW`: `∫_0^∞ |P_a(s/σ) − e^{−s²/2}| ds → 0`.
* `lemmaW_uniform`: `(1/π) ∫_0^∞ cos(zs) P_a(s/σ) ds → (2π)^{−1/2} e^{−z²/2}`, uniformly in `z`.
-/

open Real Filter Topology MeasureTheory Set

@[expose] public section

namespace CpsLean

theorem le_zeroDen {a γ : ℝ} (hA : 0 < a + 1 / 2) (hγ : 0 < γ) : a + 1 / 2 ≤ zeroDen a γ :=
  (pow_le_pow_iff_left₀ hA.le (zeroDen_pos a hγ).le two_ne_zero).mp (by
    rw [zeroDen_sq]
    nlinarith [sq_nonneg γ])

theorem zeroDen_le {a γ : ℝ} (hA : 0 < a + 1 / 2) (hγ : 0 < γ) (hle : γ ≤ a + 1 / 2) :
    zeroDen a γ ≤ √2 * (a + 1 / 2) :=
  (pow_le_pow_iff_left₀ (zeroDen_pos a hγ).le (by positivity) two_ne_zero).mp (by
    rw [zeroDen_sq, mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith)

section Enum

variable {lam : ℕ → ℝ}

theorem tendsto_prod_exp (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) (a s : ℝ) :
    Tendsto (fun N => ∏ n ∈ Finset.range N, exp (-((2 * s / zeroDen a (lam n)) ^ 2 / 4))) atTop
      (𝓝 (exp (-(s ^ 2 * sigmaSq a / 2)))) := by
  have hsum := summable_two_div hN hRH hmono hrange a
  have hs : HasSum (fun n => (2 * s / zeroDen a (lam n)) ^ 2 / 4) (s ^ 2 * sigmaSq a / 2) := by
    have := hsum.hasSum.mul_left (s ^ 2 / 2)
    rw [← sigmaSq_eq_tsum hmono hrange] at this
    convert this using 1
    · funext n
      rw [div_pow]
      ring
    · ring
  have := (continuous_exp.tendsto _).comp hs.tendsto_sum_nat.neg
  refine this.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]

/-- For `|ξ| ≤ A`: `0 ≤ P_a(ξ) ≤ e^{−ξ²σ²/2}`. -/
theorem prodJ_central (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) {a ξ : ℝ}
    (hA : 0 < a + 1 / 2) (hξ : |ξ| ≤ a + 1 / 2) :
    0 ≤ prodJ a ξ ∧ prodJ a ξ ≤ exp (-(ξ ^ 2 * sigmaSq a / 2)) := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  have hJ : ∀ n, 0 ≤ besselJ0 (2 * ξ / zeroDen a (lam n)) ∧
      besselJ0 (2 * ξ / zeroDen a (lam n)) ≤ exp (-((2 * ξ / zeroDen a (lam n)) ^ 2 / 4)) := fun n => by
    refine lemmaJ ?_
    have hd := zeroDen_pos a (hpos n)
    rw [abs_div, abs_mul, abs_two, abs_of_pos hd, div_le_iff₀ hd]
    have := le_zeroDen hA (hpos n)
    linarith
  have hlim := tendsto_prod_prodJ hN hRH a ξ hmono hrange
  have hE := tendsto_prod_exp hN hRH hmono hrange a ξ
  exact ⟨ge_of_tendsto' hlim fun N => Finset.prod_nonneg fun n _ => (hJ n).1,
    le_of_tendsto_of_tendsto' hlim hE fun N =>
      Finset.prod_le_prod₀ (fun n _ => (hJ n).1) fun n _ => (hJ n).2⟩

/-- For `|ξ| ≥ A`, if `4 + m` zeros have `0 < γ ≤ A`: `|P_a(ξ)| ≤ C⁴A²/(2ξ²) · θ^m`. -/
theorem abs_prodJ_tail (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis)
    (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates)
    {C θ : ℝ} (hC : ∀ x : ℝ, 1 ≤ |x| → |besselJ0 x| ≤ C / √|x|)
    (hθ : ∀ u : ℝ, √2 ≤ |u| → |besselJ0 u| ≤ θ) {a ξ : ℝ} (hA : 0 < a + 1 / 2)
    (hξ : a + 1 / 2 ≤ |ξ|) (m : ℕ) (hlam : ∀ n, n < 4 + m → lam n ≤ a + 1 / 2) :
    |prodJ a ξ| ≤ C ^ 4 * (a + 1 / 2) ^ 2 / (2 * ξ ^ 2) * θ ^ m := by
  have hC0 : 0 ≤ C := by
    have := hC 1 (by simp)
    have h0 := abs_nonneg (besselJ0 1)
    simpa using h0.trans this
  set A := a + 1 / 2 with hAdef
  have hξ0 : 0 < |ξ| := by linarith
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs21 : 1 ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  set w := √2 * |ξ| / A with hw
  have hw2 : √2 ≤ w := by
    rw [hw, le_div_iff₀ hA]
    exact mul_le_mul_of_nonneg_left hξ hs2.le
  have hx : ∀ n, n < 4 + m → w ≤ |2 * ξ / zeroDen a (lam n)| := fun n hn => by
    have hd := zeroDen_pos a (hpos n)
    rw [abs_div, abs_mul, abs_two, abs_of_pos hd, le_div_iff₀ hd]
    have h1 := zeroDen_le hA (hpos n) (hlam n hn)
    have hw0 : 0 ≤ w := hs2.le.trans hw2
    calc w * zeroDen a (lam n) ≤ w * (√2 * A) := mul_le_mul_of_nonneg_left h1 hw0
      _ = (√2 * √2) * |ξ| := by
          rw [hw]
          field_simp
      _ = 2 * |ξ| := by rw [hss]
  set B := C / √w with hB
  have hw0 : 0 < w := hs2.trans_le hw2
  have hsw : 0 < √w := Real.sqrt_pos.mpr hw0
  have hB0 : 0 ≤ B := by positivity
  have hJB : ∀ n, n < 4 + m → |besselJ0 (2 * ξ / zeroDen a (lam n))| ≤ B := fun n hn => by
    have h1 := hx n hn
    refine (hC _ (hs21.trans (hw2.trans h1))).trans ?_
    exact div_le_div_of_nonneg_left hC0 hsw (Real.sqrt_le_sqrt h1)
  have hB4 : B ^ 4 = C ^ 4 * A ^ 2 / (2 * ξ ^ 2) := by
    have e1 : (√w) ^ 4 = w ^ 2 := by
      have : (√w) ^ 4 = ((√w) ^ 2) ^ 2 := by ring
      rw [this, Real.sq_sqrt hw0.le]
    have e2 : w ^ 2 = 2 * ξ ^ 2 / A ^ 2 := by
      rw [hw, div_pow, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
    rw [hB, div_pow, e1, e2]
    have hξ2 : ξ ≠ 0 := abs_pos.mp hξ0
    field_simp
  refine (abs_prodJ_le_prod hN hRH a ξ hmono hrange (4 + m)).trans ?_
  rw [Finset.prod_range_add, ← hB4]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
  · calc ∏ n ∈ Finset.range 4, |besselJ0 (2 * ξ / zeroDen a (lam n))|
        ≤ ∏ _n ∈ Finset.range 4, B :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun n hn =>
            hJB n (by have := Finset.mem_range.mp hn; omega)
      _ = B ^ 4 := by simp
  · calc ∏ n ∈ Finset.range m, |besselJ0 (2 * ξ / zeroDen a (lam (4 + n)))|
        ≤ ∏ _n ∈ Finset.range m, θ :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun n hn => by
            have h1 := hx (4 + n) (by have := Finset.mem_range.mp hn; omega)
            exact hθ _ (hw2.trans h1)
      _ = θ ^ m := by simp

/-- At least `⌊A⌋` zeros have `0 < γ ≤ A`, for `A` large. -/
theorem eventually_lam_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI)
    (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates) :
    ∀ᶠ A : ℝ in atTop, ∀ n, n < ⌊A⌋₊ → lam n ≤ A := by
  obtain ⟨C, hC0, hC⟩ := exists_zeroCount_sub_le hN hRH hLI hmono hpos hrange
  have hL : Tendsto (fun A : ℝ => log (A / (2 * π))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hL.eventually_ge_atTop (1 + 4 * π),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (2 * C)] with A h1 h2 h3 n hn
  by_contra hlt
  push Not at hlt
  have hA0 : 0 ≤ A := by linarith
  have hN' := (abs_le.mp (hC A hA0)).1
  have hsum := hasSum_zeroCount hRH hLI hmono hpos hrange A
  have hzero : ∀ k ∉ Finset.range n, (Ici (lam k)).indicator (fun _ => (1 : ℝ)) A = 0 := fun k hk => by
    have hk2 : n ≤ k := by simpa using hk
    have : A < lam k := hlt.trans_le (hmono.monotone hk2)
    exact indicator_of_notMem (by simpa using this) _
  have heq := hsum.unique (hasSum_sum_of_ne_finset_zero hzero)
  have hle : (zeroCount A : ℝ) ≤ n := by
    rw [heq]
    calc ∑ k ∈ Finset.range n, (Ici (lam k)).indicator (fun _ => (1 : ℝ)) A
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          by_cases h : A ∈ Ici (lam k)
          · rw [indicator_of_mem h]
          · rw [indicator_of_notMem h]
            norm_num
      _ = n := by simp
  have hnA : (n : ℝ) + 1 ≤ A := by
    have h4 : ((n + 1 : ℕ) : ℝ) ≤ (⌊A⌋₊ : ℝ) := by exact_mod_cast hn
    have h5 := Nat.floor_le hA0
    push_cast at h4
    linarith
  have hF : 2 * A ≤ rvmF A := by
    unfold rvmF
    have hk : 0 ≤ A / (2 * π) := by positivity
    have := mul_le_mul_of_nonneg_left h2 hk
    have e : A / (2 * π) * (1 + 4 * π) = A / (2 * π) + 2 * A := by
      field_simp
      ring
    linarith
  set s := √A with hs
  have hss : s * s = A := Real.mul_self_sqrt hA0
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr h1
  have hbound : C * (1 + s) ≤ A := by
    have h5 : C * (1 + s) ≤ 2 * C * s := by nlinarith
    have h6 : 2 * C * s ≤ s * s := mul_le_mul_of_nonneg_right h3 (by linarith)
    linarith
  linarith

end Enum

theorem measurable_prodJ (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a : ℝ) :
    Measurable (prodJ a) := by
  obtain ⟨lam, hmono, _, hrange, _⟩ := exists_ordinate_enum hN
  refine measurable_of_tendsto_metrizable
    (f := fun N ξ => ∏ n ∈ Finset.range N, besselJ0 (2 * ξ / zeroDen a (lam n))) (fun N => ?_)
    (tendsto_pi_nhds.mpr fun ξ => tendsto_prod_prodJ hN hRH a ξ hmono hrange)
  exact Finset.measurable_fun_prod _ fun n _ => (continuous_besselJ0.comp (by fun_prop)).measurable

theorem integrable_prodJ (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hB : BesselDecay)
    (a : ℝ) : Integrable (prodJ a) := by
  obtain ⟨K, hK⟩ := exists_prodJ_le_inv hN hRH hB a
  exact Integrable.mono' (integrable_inv_one_add_sq.const_mul K)
    (measurable_prodJ hN hRH a).aestronglyMeasurable (ae_of_all _ fun ξ => hK ξ)

theorem integrable_gauss : Integrable fun s : ℝ => exp (-(s ^ 2 / 2)) := by
  have h : Integrable fun s : ℝ => exp (-(1 / 2) * s ^ 2) := integrable_exp_neg_mul_sq (by norm_num)
  refine h.congr (ae_of_all _ fun s => ?_)
  simp only
  congr 1
  ring

theorem integrableOn_inv_sq {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => (s ^ 2)⁻¹) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc).congr_fun (fun s hs => ?_)
    measurableSet_Ioi
  have hs0 : 0 < s := hc.trans hs
  change s ^ (-2 : ℝ) = (s ^ 2)⁻¹
  rw [Real.rpow_neg hs0.le, Real.rpow_two]

theorem integral_inv_sq {c : ℝ} (hc : 0 < c) : ∫ s in Ioi c, (s ^ 2)⁻¹ = c⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc
  have e : ∫ s in Ioi c, (s ^ 2)⁻¹ = ∫ s in Ioi c, s ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hc.trans hs
    rw [Real.rpow_neg hs0.le, Real.rpow_two]
  rw [e, h]
  norm_num
  rw [Real.rpow_neg_one]

/-- The pointwise bound behind Lemma W. -/
theorem abs_prodJ_scaled_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) {a : ℝ}
    (hA : a + 1 / 2 ≠ 0) (s : ℝ) :
    |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))| ≤
      s ^ 4 * ((a + 1 / 2) ^ 2 * sigmaSq a)⁻¹ := by
  have hpos := sigmaSq_pos hN hRH a
  have h := abs_prodJ_sub_exp_le hN hRH hA (s / √(sigmaSq a))
  have e2 : (s / √(sigmaSq a)) ^ 2 = s ^ 2 / sigmaSq a := by
    rw [div_pow, Real.sq_sqrt hpos.le]
  have e1 : (s / √(sigmaSq a)) ^ 2 * sigmaSq a / 2 = s ^ 2 / 2 := by
    rw [e2]
    field_simp
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have e3 : (s / √(sigmaSq a)) ^ 4 = (s ^ 2 / sigmaSq a) ^ 2 := by
    rw [← e2]
    ring
  rw [e3]
  field_simp

/-- `∫_0^∞ |P_a(s/σ) − e^{−s²/2}| ds`, split at `s = Aσ`. -/
theorem integral_gap_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hB : BesselDecay)
    {lam : ℕ → ℝ} (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates)
    {C θ : ℝ} (hC : ∀ x : ℝ, 1 ≤ |x| → |besselJ0 x| ≤ C / √|x|)
    (hθ : ∀ u : ℝ, √2 ≤ |u| → |besselJ0 u| ≤ θ) (hθ0 : 0 ≤ θ) {a : ℝ} (hA : 0 < a + 1 / 2) (m : ℕ)
    (hlam : ∀ n, n < 4 + m → lam n ≤ a + 1 / 2) :
    ∫ s in Ioi (0 : ℝ), |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))| ≤
      (∫ s in Ioi (0 : ℝ), min |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))|
        (2 * exp (-(s ^ 2 / 2)))) +
      C ^ 4 / 2 * ((a + 1 / 2) * √(sigmaSq a)) * θ ^ m := by
  have hC0 : 0 ≤ C := by
    have := hC 1 (by simp)
    have h0 := abs_nonneg (besselJ0 1)
    simpa using h0.trans this
  have hsp := sigmaSq_pos hN hRH a
  set σ := √(sigmaSq a) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hsp
  have hσsq : σ ^ 2 = sigmaSq a := Real.sq_sqrt hsp.le
  set A := a + 1 / 2 with hAdef
  set c := A * σ with hc
  have hc0 : 0 < c := by positivity
  have hP : Integrable fun s : ℝ => prodJ a (s / σ) := (integrable_prodJ hN hRH hB a).comp_div hσ0.ne'
  have hg : Integrable fun s : ℝ => |prodJ a (s / σ) - exp (-(s ^ 2 / 2))| :=
    (hP.sub integrable_gauss).abs
  have hd : Integrable fun s : ℝ => min |prodJ a (s / σ) - exp (-(s ^ 2 / 2))|
      (2 * exp (-(s ^ 2 / 2))) := by
    refine Integrable.mono' (integrable_gauss.const_mul 2) ?_ (ae_of_all _ fun s => ?_)
    · exact (hg.aestronglyMeasurable.aemeasurable.min
        (integrable_gauss.const_mul 2).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (by positivity))]
      exact min_le_right _ _
  have hT : Integrable ((Ioi c).indicator fun s : ℝ => |prodJ a (s / σ)|) :=
    hP.abs.indicator measurableSet_Ioi
  have hpt : ∀ s ∈ Ioi (0 : ℝ), |prodJ a (s / σ) - exp (-(s ^ 2 / 2))| ≤
      min |prodJ a (s / σ) - exp (-(s ^ 2 / 2))| (2 * exp (-(s ^ 2 / 2))) +
        (Ioi c).indicator (fun s : ℝ => |prodJ a (s / σ)|) s := by
    intro s hs0
    have hs : (0 : ℝ) < s := hs0
    have he := exp_pos (-(s ^ 2 / 2))
    by_cases hsc : s ∈ Ioi c
    · rw [indicator_of_mem hsc]
      have htri : |prodJ a (s / σ) - exp (-(s ^ 2 / 2))| ≤ |prodJ a (s / σ)| + exp (-(s ^ 2 / 2)) := by
        have := abs_sub (prodJ a (s / σ)) (exp (-(s ^ 2 / 2)))
        rwa [abs_of_pos he] at this
      rcases le_total |prodJ a (s / σ) - exp (-(s ^ 2 / 2))| (2 * exp (-(s ^ 2 / 2))) with h | h
      · rw [min_eq_left h]
        linarith [abs_nonneg (prodJ a (s / σ))]
      · rw [min_eq_right h]
        linarith
    · rw [indicator_of_notMem hsc, add_zero]
      have hsc2 : s ≤ c := not_lt.mp hsc
      have hξ : |s / σ| ≤ A := by
        rw [abs_of_pos (div_pos hs hσ0), div_le_iff₀ hσ0]
        exact hsc2
      obtain ⟨h1, h2⟩ := prodJ_central hN hRH hA hξ
      have e : (s / σ) ^ 2 * sigmaSq a / 2 = s ^ 2 / 2 := by
        rw [← hσsq]
        field_simp
      rw [e] at h2
      refine le_min le_rfl ?_
      rw [abs_le]
      constructor <;> linarith
  have h1 := setIntegral_mono_on hg.integrableOn (hd.add hT).integrableOn measurableSet_Ioi hpt
  rw [integral_add' hd.integrableOn hT.integrableOn] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi c = Ioi c from inter_eq_right.mpr (Ioi_subset_Ioi hc0.le)]
  -- the tail
  set Q := C ^ 4 * A ^ 2 * σ ^ 2 / 2 * θ ^ m with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hint := (integrableOn_inv_sq hc0).const_mul Q
  have htail : ∀ s ∈ Ioi c, |prodJ a (s / σ)| ≤ Q * (s ^ 2)⁻¹ := by
    intro s hs
    have hs1 : c < s := hs
    have hs0 : 0 < s := hc0.trans hs1
    have hξ : A ≤ |s / σ| := by
      rw [abs_of_pos (div_pos hs0 hσ0), le_div_iff₀ hσ0]
      exact hs1.le
    refine (abs_prodJ_tail hN hRH hmono hpos hrange hC hθ hA hξ m hlam).trans (le_of_eq ?_)
    rw [hQ, div_pow]
    field_simp
    rw [hAdef]
    ring
  refine (setIntegral_mono_on hP.abs.integrableOn hint measurableSet_Ioi htail).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_inv_sq hc0, hQ, hc]
  field_simp

theorem tendsto_A_mul_sigma (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    Tendsto (fun a : ℝ => (a + 1 / 2) * √(sigmaSq a)) atTop atTop := by
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  refine (Real.tendsto_sqrt_atTop.comp (tendsto_sq_mul_sigmaSq hN hRH hLI)).congr' ?_
  filter_upwards [hAt.eventually_gt_atTop 0] with a ha
  simp only [Function.comp_apply]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha.le]

theorem tendsto_sigmaSq_zero (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    Tendsto sigmaSq atTop (𝓝 0) := by
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hx : Tendsto (fun a : ℝ => (a + 1 / 2) / (2 * π)) atTop atTop :=
    hAt.atTop_div_const (by positivity)
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (4 * π) 0 1 (by positivity)).comp hx
  refine (sigmaSq_isEquivalent hN hRH hLI).symm.tendsto_nhds (h.congr' ?_)
  filter_upwards [hAt.eventually_gt_atTop 0] with a ha
  simp only [Function.comp_apply, pow_one, add_zero]
  congr 1
  field_simp
  ring

/-- **Lemma W.** `∫_0^∞ |P_a(s/σ_a) − e^{−s²/2}| ds → 0` as `a → ∞`. -/
theorem lemmaW (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) (hB : BesselDecay) :
    Tendsto (fun a : ℝ => ∫ s in Ioi (0 : ℝ), |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))|)
      atTop (𝓝 0) := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_theta hB
  obtain ⟨C, hC⟩ := hB
  have hC0 : 0 ≤ C := by
    have := hC 1 (by simp)
    have h0 := abs_nonneg (besselJ0 1)
    simpa using h0.trans this
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hgmeas : ∀ a : ℝ, Measurable fun s : ℝ => |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))| :=
    fun a => by
      have hP := measurable_prodJ hN hRH a
      fun_prop
  -- the part dominated by the Gaussian
  have hd : Tendsto (fun a : ℝ => ∫ s in Ioi (0 : ℝ), min |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))|
      (2 * exp (-(s ^ 2 / 2)))) atTop (𝓝 0) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ))) (l := (atTop : Filter ℝ))
      (F := fun (a : ℝ) (s : ℝ) => min |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))|
        (2 * exp (-(s ^ 2 / 2)))) (f := fun _ => (0 : ℝ))
      (fun s : ℝ => 2 * exp (-(s ^ 2 / 2)))
      (Eventually.of_forall fun a => ((hgmeas a).min (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun a => ae_of_all _ fun s => by
        rw [Real.norm_of_nonneg (le_min (abs_nonneg _) (by positivity))]
        exact min_le_right _ _)
      (integrable_gauss.const_mul 2).integrableOn
      (ae_of_all _ fun s => by
        have hinv := (tendsto_sq_mul_sigmaSq hN hRH hLI).inv_tendsto_atTop
        have hb : Tendsto (fun a : ℝ => s ^ 4 * ((a + 1 / 2) ^ 2 * sigmaSq a)⁻¹) atTop (𝓝 0) := by
          simpa using hinv.const_mul (s ^ 4)
        refine squeeze_zero' (Eventually.of_forall fun a =>
          le_min (abs_nonneg _) (by positivity)) ?_ hb
        filter_upwards [hAt.eventually_gt_atTop 0] with a ha
        exact (min_le_left _ _).trans (abs_prodJ_scaled_le hN hRH ha.ne' s))
    simpa using hlim
  -- the tail
  have hpow : Tendsto (fun m : ℕ => C ^ 4 / 2 * (((m : ℝ) + 5) * θ ^ m)) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hθ0 hθ1
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul (5 : ℝ)
    have h3 := (h1.add h2).const_mul (C ^ 4 / 2)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun m => ?_
    ring
  have hfloor : Tendsto (fun a : ℝ => ⌊a + 1 / 2⌋₊ - 4) atTop atTop :=
    (tendsto_sub_atTop_nat 4).comp (tendsto_nat_floor_atTop.comp hAt)
  have hE := hpow.comp hfloor
  have hsq1 : ∀ᶠ a : ℝ in atTop, sigmaSq a < 1 :=
    (tendsto_sigmaSq_zero hN hRH hLI).eventually_lt_const one_pos
  have hsum := hd.add hE
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun a => setIntegral_nonneg measurableSet_Ioi
    fun s _ => abs_nonneg _) ?_ hsum
  filter_upwards [hsq1, hAt.eventually_ge_atTop (5 : ℝ),
    hAt.eventually (eventually_lam_le hN hRH hLI hmono hpos hrange)] with a hs1 hA5 hlam
  have hA0 : 0 < a + 1 / 2 := by linarith
  have hfl : 4 ≤ ⌊a + 1 / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  set m := ⌊a + 1 / 2⌋₊ - 4 with hm
  have hm4 : 4 + m = ⌊a + 1 / 2⌋₊ := by omega
  refine (integral_gap_le hN hRH ⟨C, hC⟩ hmono hpos hrange hC hθ hθ0 hA0 m (by rw [hm4]; exact hlam)).trans ?_
  simp only [Function.comp_apply]
  refine add_le_add le_rfl ?_
  have hσ1 : √(sigmaSq a) ≤ 1 := Real.sqrt_le_one.mpr hs1.le
  have hσ0 : 0 ≤ √(sigmaSq a) := Real.sqrt_nonneg _
  have hAm : a + 1 / 2 ≤ (m : ℝ) + 5 := by
    have := Nat.lt_floor_add_one (a + 1 / 2)
    rw [← hm4] at this
    push_cast at this
    linarith
  have hprod : (a + 1 / 2) * √(sigmaSq a) ≤ (m : ℝ) + 5 := by
    nlinarith
  have hθm : 0 ≤ θ ^ m := by positivity
  have hC4 : 0 ≤ C ^ 4 / 2 := by positivity
  calc C ^ 4 / 2 * ((a + 1 / 2) * √(sigmaSq a)) * θ ^ m
      ≤ C ^ 4 / 2 * ((m : ℝ) + 5) * θ ^ m := by gcongr
    _ = _ := by ring

/-- `∫_0^∞ e^{−s²/2} ds = √(2π)/2`. -/
theorem integral_gauss_Ioi : ∫ s in Ioi (0 : ℝ), exp (-(s ^ 2 / 2)) = √(2 * π) / 2 := by
  have h := integral_gaussian_Ioi (1 / 2)
  have e : ∫ s in Ioi (0 : ℝ), exp (-(s ^ 2 / 2)) = ∫ s in Ioi (0 : ℝ), exp (-(1 / 2) * s ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 1
    ring
  rw [e, h]
  congr 2
  field_simp

/-- `∫_0^∞ cos(zs) e^{−s²/2} ds = (√(2π)/2) e^{−z²/2}`. -/
theorem integral_cos_gauss (z : ℝ) :
    ∫ s in Ioi (0 : ℝ), cos (z * s) * exp (-(s ^ 2 / 2)) = √(2 * π) / 2 * exp (-(z ^ 2 / 2)) := by
  have hF := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) (z : ℂ)
  have hint : Integrable fun s : ℝ => Complex.exp (Complex.I * z * s) * Complex.exp (-(1 / 2 : ℂ) * s ^ 2) := by
    have h0 : Integrable fun s : ℝ => Complex.exp (-(1 / 2 : ℂ) * s ^ 2) :=
      integrable_cexp_neg_mul_sq (by norm_num)
    refine h0.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun s => ?_)
    have e : Complex.I * (z : ℂ) * (s : ℂ) = ((z * s : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hre := Complex.reCLM.integral_comp_comm hint
  rw [hF] at hre
  have hterm : ∀ s : ℝ, Complex.reCLM (Complex.exp (Complex.I * z * s) *
      Complex.exp (-(1 / 2 : ℂ) * s ^ 2)) = cos (z * |s|) * exp (-(|s| ^ 2 / 2)) := fun s => by
    have e : Complex.I * (z : ℂ) * (s : ℂ) = ((z * s : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have e2 : -(1 / 2 : ℂ) * (s : ℂ) ^ 2 = ((-(s ^ 2 / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, e2, ← Complex.ofReal_exp, Complex.reCLM_apply, Complex.re_mul_ofReal,
      Complex.exp_ofReal_mul_I_re, sq_abs]
    rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, cos_neg]
  simp_rw [hterm] at hre
  have habs := integral_comp_abs (f := fun s => cos (z * s) * exp (-(s ^ 2 / 2)))
  rw [habs] at hre
  have hval : Complex.reCLM (((π : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
      Complex.exp (-(z : ℂ) ^ 2 / (4 * (1 / 2)))) = √(2 * π) * exp (-(z ^ 2 / 2)) := by
    have e1 : ((π : ℂ) / (1 / 2)) = ((2 * π : ℝ) : ℂ) := by
      push_cast
      ring
    have e2 : -(z : ℂ) ^ 2 / (4 * (1 / 2)) = ((-(z ^ 2 / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    have e3 : ((2 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (√(2 * π) : ℝ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
      norm_num
    rw [e1, e2, e3, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.reCLM_apply, Complex.ofReal_re]
  rw [hval] at hre
  linarith

/-- **Lemma W, uniform in `z`.** The local limit theorem:
`(1/π) ∫_0^∞ cos(zs) P_a(s/σ_a) ds → (2π)^{−1/2} e^{−z²/2}`, uniformly in `z`. -/
theorem lemmaW_uniform (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) (hB : BesselDecay) :
    TendstoUniformly (fun (a : ℝ) (z : ℝ) =>
        1 / π * ∫ s in Ioi (0 : ℝ), cos (z * s) * prodJ a (s / √(sigmaSq a)))
      (fun z => (√(2 * π))⁻¹ * exp (-(z ^ 2 / 2))) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hpi : 0 < π := pi_pos
  have hW := lemmaW hN hRH hLI hB
  filter_upwards [hW.eventually_lt_const (show 0 < π * ε by positivity)] with a ha z
  have hsp := sigmaSq_pos hN hRH a
  have hσ0 : 0 < √(sigmaSq a) := Real.sqrt_pos.mpr hsp
  have hP : Integrable fun s : ℝ => prodJ a (s / √(sigmaSq a)) :=
    (integrable_prodJ hN hRH hB a).comp_div hσ0.ne'
  have hb : Measurable fun s : ℝ => cos (z * s) := by fun_prop
  have hi1 : Integrable fun s : ℝ => cos (z * s) * prodJ a (s / √(sigmaSq a)) :=
    hP.bdd_mul (c := 1) hb.aestronglyMeasurable (ae_of_all _ fun s => by
      simpa using abs_cos_le_one (z * s))
  have hi2 : Integrable fun s : ℝ => cos (z * s) * exp (-(s ^ 2 / 2)) :=
    integrable_gauss.bdd_mul (c := 1) hb.aestronglyMeasurable (ae_of_all _ fun s => by
      simpa using abs_cos_le_one (z * s))
  have hval : (√(2 * π))⁻¹ * exp (-(z ^ 2 / 2)) =
      1 / π * ∫ s in Ioi (0 : ℝ), cos (z * s) * exp (-(s ^ 2 / 2)) := by
    rw [integral_cos_gauss, ← mul_assoc]
    congr 1
    have hr : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
    have hrr : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
    field_simp
    linarith
  rw [hval, dist_eq_norm, ← mul_sub, ← integral_sub hi2.integrableOn hi1.integrableOn, norm_mul,
    Real.norm_of_nonneg (by positivity)]
  have hnorm : ‖∫ s in Ioi (0 : ℝ), (cos (z * s) * exp (-(s ^ 2 / 2)) -
      cos (z * s) * prodJ a (s / √(sigmaSq a)))‖ ≤
      ∫ s in Ioi (0 : ℝ), |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))| := by
    refine norm_integral_le_of_norm_le (hP.sub integrable_gauss).abs.integrableOn
      (ae_of_all _ fun s => ?_)
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)
  calc 1 / π * ‖∫ s in Ioi (0 : ℝ), (cos (z * s) * exp (-(s ^ 2 / 2)) -
        cos (z * s) * prodJ a (s / √(sigmaSq a)))‖
      ≤ 1 / π * ∫ s in Ioi (0 : ℝ), |prodJ a (s / √(sigmaSq a)) - exp (-(s ^ 2 / 2))| :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ < 1 / π * (π * ε) := mul_lt_mul_of_pos_left ha (by positivity)
    _ = ε := by field_simp

end CpsLean
