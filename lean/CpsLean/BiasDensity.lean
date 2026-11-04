module

public import CpsLean.ProdJ
set_option autoImplicit false

/-!
# Theorem 3(ii): the density of the race under LI

* `deltaA a = ½ − (1/π) ∫_0^∞ sin(ξ/(2a+1))/ξ · Π_{γ>0} J₀(2ξ/|½+a+iγ|) dξ`.
* `HasLogDensity S d`: `(1/log X) ∫_2^X 1_S(x) dx/x → d`.
* `shiftLaw μ b`: the law of `t + b` under `μ`. With `b = 1/(2a+1)` it is the symmetric part of `μ_a`.
* `theorem3_ii`: **Theorem 3(ii)**.
-/

open Real Filter Topology MeasureTheory Set ProbabilityTheory

@[expose] public section

namespace CpsLean

/-- `δ_a = ½ − (1/π) ∫_0^∞ sin(ξ/(2a+1))/ξ · Π_{γ>0} J₀(2ξ/|½+a+iγ|) dξ`. -/
noncomputable def deltaA (a : ℝ) : ℝ :=
  1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ

/-- `S` has logarithmic density `d`: `(1/log X) ∫_2^X 1_S(x) dx/x → d`. -/
def HasLogDensity (S : Set ℝ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℝ => (1 / log X) * ∫ x in (2 : ℝ)..X, S.indicator (fun x => 1 / x) x) atTop (𝓝 d)

/-- The law of `t + b` under `μ`. -/
noncomputable def shiftLaw (μ : ProbabilityMeasure ℝ) (b : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(μ : Measure ℝ).map (· + b), Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance⟩

theorem coe_shiftLaw (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    ((shiftLaw μ b : ProbabilityMeasure ℝ) : Measure ℝ) = (μ : Measure ℝ).map (· + b) := rfl

section Limiting

variable {a : ℝ} {μ : ProbabilityMeasure ℝ}

/-- The symmetric part of `μ_a` has characteristic function `P`. -/
theorem charFun_shiftLaw (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hRH : RiemannHypothesis) (hLI : LI)
    (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) (ξ : ℝ) :
    charFun ((shiftLaw μ (1 / (2 * a + 1)) : ProbabilityMeasure ℝ) : Measure ℝ) ξ =
      (prodJ a ξ : ℂ) := by
  rw [coe_shiftLaw, charFun_map_add_const, charFun_apply_real]
  have h := integral_exp_limiting hE hN hK h19 hRH hLI ha hμ ξ
  have e : ∀ t : ℝ, Complex.exp ((ξ : ℂ) * (t : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) := fun t => by
    congr 1
    ring
  simp_rw [e]
  rw [h, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  have e2 : Complex.I * ((-1 / (2 * a + 1) : ℝ) : ℂ) * (ξ : ℂ) +
      ((inner ℝ (1 / (2 * a + 1)) ξ : ℝ) : ℂ) * Complex.I = 0 := by
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [e2]
  simp

theorem symm_shiftLaw (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hRH : RiemannHypothesis) (hLI : LI)
    (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) :
    ((shiftLaw μ (1 / (2 * a + 1)) : ProbabilityMeasure ℝ) : Measure ℝ).map (fun t => -t) =
      (shiftLaw μ (1 / (2 * a + 1)) : ProbabilityMeasure ℝ) := by
  refine Measure.ext_of_charFun ?_
  funext ξ
  have e : (fun t : ℝ => -t) = ((-1 : ℝ) * ·) := by
    funext t
    ring
  rw [e, charFun_map_mul, charFun_shiftLaw hE hN hK h19 hRH hLI ha hμ,
    charFun_shiftLaw hE hN hK h19 hRH hLI ha hμ, neg_one_mul, prodJ_neg]

/-- `P` is bounded by `K/(1+ξ²)`. -/
theorem exists_prodJ_le_inv (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hB : BesselDecay)
    (a : ℝ) : ∃ K : ℝ, ∀ ξ : ℝ, |prodJ a ξ| ≤ K * (1 + ξ ^ 2)⁻¹ := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  obtain ⟨K, ξ₀, hK, hξ₀, h⟩ := abs_prodJ_le_pow hN hRH hB a hmono hpos hrange 4
  set ξ₁ := max ξ₀ 1 with hξ₁
  refine ⟨2 * K + 1 + ξ₁ ^ 2, fun ξ => ?_⟩
  have hpos1 : 0 < 1 + ξ ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos1]
  rcases le_or_gt ξ₁ |ξ| with hξ | hξ
  · have h1 : ξ₀ ≤ |ξ| := (le_max_left _ _).trans hξ
    have h2 : 1 ≤ |ξ| := (le_max_right _ _).trans hξ
    have hsq : 1 ≤ ξ ^ 2 := by nlinarith [sq_abs ξ]
    have hb := h ξ h1
    have hp : ((√|ξ|)⁻¹) ^ 4 = (ξ ^ 2)⁻¹ := by
      rw [inv_pow]
      congr 1
      have : (√|ξ|) ^ 4 = ((√|ξ|) ^ 2) ^ 2 := by ring
      rw [this, Real.sq_sqrt (abs_nonneg ξ), sq_abs]
    rw [hp] at hb
    have hξ2 : 0 < ξ ^ 2 := by positivity
    have : |prodJ a ξ| * ξ ^ 2 ≤ K := by
      calc |prodJ a ξ| * ξ ^ 2 ≤ K * (ξ ^ 2)⁻¹ * ξ ^ 2 := mul_le_mul_of_nonneg_right hb hξ2.le
        _ = K := by rw [mul_assoc, inv_mul_cancel₀ hξ2.ne', mul_one]
    have h3 := abs_nonneg (prodJ a ξ)
    nlinarith [sq_nonneg ξ₁]
  · have h1 := abs_prodJ_le_one hN hRH a ξ
    have h3 := abs_nonneg (prodJ a ξ)
    have hsq : ξ ^ 2 ≤ ξ₁ ^ 2 := by
      rw [← sq_abs ξ]
      exact pow_le_pow_left₀ (abs_nonneg _) hξ.le 2
    nlinarith [sq_nonneg ξ]

theorem integrable_charFun_shiftLaw (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay) (hRH : RiemannHypothesis)
    (hLI : LI) (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) :
    Integrable (charFun ((shiftLaw μ (1 / (2 * a + 1)) : ProbabilityMeasure ℝ) : Measure ℝ)) := by
  obtain ⟨K, hK'⟩ := exists_prodJ_le_inv hN hRH hB a
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) ?_ (ae_of_all _ fun ξ => ?_)
  · exact measurable_charFun.aestronglyMeasurable
  · rw [charFun_shiftLaw hE hN hK h19 hRH hLI ha hμ, Complex.norm_real, Real.norm_eq_abs]
    exact hK' ξ

/-- `μ(0, ∞) = ν(b, ∞)`, where `ν` is the law of `t + b`. -/
theorem real_shiftLaw_Ioi (μ : ProbabilityMeasure ℝ) (b : ℝ) :
    ((shiftLaw μ b : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi b) = (μ : Measure ℝ).real (Ioi 0) := by
  rw [coe_shiftLaw, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext t
  simp

/-- `δ_a = ν(b, ∞)`, the inversion formula for the symmetric part. -/
theorem deltaA_eq (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI)
    (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) :
    (μ : Measure ℝ).real (Ioi 0) = deltaA a := by
  have hb : 0 < 1 / (2 * a + 1) := by
    have : 0 < 2 * a + 1 := by linarith
    positivity
  rw [← real_shiftLaw_Ioi μ (1 / (2 * a + 1)),
    hRS _ (symm_shiftLaw hE hN hK h19 hRH hLI ha hμ)
      (integrable_charFun_shiftLaw hE hN hK h19 hB hRH hLI ha hμ) _ hb]
  unfold deltaA
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
  rw [charFun_shiftLaw hE hN hK h19 hRH hLI ha hμ, Complex.ofReal_re]
  congr 3
  ring

/-- `μ` is symmetric about `−1/(2a+1)`. -/
theorem symm_limiting (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hRH : RiemannHypothesis) (hLI : LI)
    (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) :
    (μ : Measure ℝ).map (fun t => 2 * (-1 / (2 * a + 1)) - t) = μ := by
  refine Measure.ext_of_charFun ?_
  funext ξ
  rw [charFun_apply_real, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  set c : ℝ := -1 / (2 * a + 1) with hc
  have hval : ∀ ζ : ℝ, ∫ t, Complex.exp (Complex.I * (ζ : ℂ) * (t : ℂ)) ∂(μ : Measure ℝ) =
      Complex.exp (Complex.I * (c : ℂ) * (ζ : ℂ)) * (prodJ a ζ : ℂ) :=
    fun ζ => integral_exp_limiting hE hN hK h19 hRH hLI ha hμ ζ
  have e1 : ∀ t : ℝ, Complex.exp ((ξ : ℂ) * ((2 * c - t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((2 * c : ℝ) : ℂ) * (ξ : ℂ)) *
        Complex.exp (Complex.I * ((-ξ : ℝ) : ℂ) * (t : ℂ)) := fun t => by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : ∀ t : ℝ, Complex.exp ((ξ : ℂ) * (t : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) := fun t => by
    congr 1
    ring
  simp_rw [e1, e2]
  rw [integral_const_mul, hval, hval, prodJ_neg, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `μ` is absolutely continuous. -/
theorem absCont_limiting (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI)
    (ha : -1 / 2 < a) (hμ : HasLimitingDistribution (phiA a) μ) :
    (μ : Measure ℝ) ≪ volume := by
  set b := 1 / (2 * a + 1) with hbdef
  have hν := absCont_of_integrable_charFun hRS (symm_shiftLaw hE hN hK h19 hRH hLI ha hμ)
    (integrable_charFun_shiftLaw hE hN hK h19 hB hRH hLI ha hμ)
  refine Measure.AbsolutelyContinuous.mk fun s hs hv => ?_
  have hpre : volume ((fun t : ℝ => t + -b) ⁻¹' s) = 0 := by
    rw [measure_preimage_add_right]
    exact hv
  have h0 := hν hpre
  rw [coe_shiftLaw, Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop))] at h0
  have e : (fun t : ℝ => t + b) ⁻¹' ((fun t : ℝ => t + -b) ⁻¹' s) = s := by
    ext t
    simp
  rwa [e] at h0

end Limiting

/-- `max 0 (min 1 (k t + s))`. -/
noncomputable def rampF (k s t : ℝ) : ℝ := max 0 (min 1 (k * t + s))

theorem continuous_rampF (k s : ℝ) : Continuous (rampF k s) := by
  unfold rampF
  fun_prop

theorem rampF_nonneg (k s t : ℝ) : 0 ≤ rampF k s t := le_max_left _ _

theorem rampF_le_one (k s t : ℝ) : rampF k s t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- `rampF` as a bounded continuous function. -/
noncomputable def rampB (k s : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (rampF k s) (continuous_rampF k s) 1 fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rampF_nonneg k s t)]
    exact rampF_le_one k s t

theorem rampB_apply (k s t : ℝ) : rampB k s t = rampF k s t := rfl

/-- The indicator of `t > 0`. -/
noncomputable def posInd (t : ℝ) : ℝ := (Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t

theorem measurable_posInd : Measurable posInd :=
  measurable_const.indicator measurableSet_Ioi

theorem rampF_zero_le_posInd {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : rampF k 0 t ≤ posInd t := by
  unfold posInd
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    exact rampF_le_one _ _ _
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    unfold rampF
    refine max_le le_rfl (min_le_of_right_le ?_)
    have := mul_nonneg hk (neg_nonneg.mpr (not_lt.mp ht))
    linarith

theorem posInd_le_rampF_one {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : posInd t ≤ rampF k 1 t := by
  unfold posInd
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    unfold rampF
    refine le_max_of_le_right (le_min le_rfl ?_)
    have := mul_nonneg hk ht.le
    linarith
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    exact rampF_nonneg _ _ _

theorem tendsto_integral_ramp (μ : ProbabilityMeasure ℝ) :
    Tendsto (fun k : ℕ => ∫ t, rampF k 0 t ∂(μ : Measure ℝ)) atTop
      (𝓝 ((μ : Measure ℝ).real (Ioi 0))) := by
  have e : (μ : Measure ℝ).real (Ioi 0) = ∫ t, posInd t ∂(μ : Measure ℝ) := by
    unfold posInd
    rw [integral_indicator_const _ measurableSet_Ioi]
    simp
  rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun k => (continuous_rampF _ _).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (rampF_nonneg _ _ _)]
    exact rampF_le_one _ _ _
  · by_cases ht : 0 < t
    · have hv : posInd t = 1 := by
        unfold posInd
        rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      rw [hv]
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / t)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      have h1 : 1 / t ≤ k := hK.trans (by exact_mod_cast hk)
      have h2 : 1 ≤ (k : ℝ) * t := by rwa [div_le_iff₀ ht] at h1
      unfold rampF
      rw [add_zero, min_eq_left h2, max_eq_right zero_le_one]
    · have hv : posInd t = 0 := by
        unfold posInd
        rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      rw [hv]
      refine tendsto_const_nhds.congr fun k => ?_
      refine le_antisymm (rampF_nonneg _ _ _) ?_
      have := rampF_zero_le_posInd (k := k) (by positivity) t
      rw [hv] at this
      exact this

theorem tendsto_integral_ramp_one (μ : ProbabilityMeasure ℝ) (h0 : (μ : Measure ℝ).real {0} = 0) :
    Tendsto (fun k : ℕ => ∫ t, rampF k 1 t ∂(μ : Measure ℝ)) atTop
      (𝓝 ((μ : Measure ℝ).real (Ioi 0))) := by
  have e : (μ : Measure ℝ).real (Ioi 0) =
      ∫ t, (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ)) t ∂(μ : Measure ℝ) := by
    rw [integral_indicator_const _ measurableSet_Ici]
    have hu : Ici (0 : ℝ) = {0} ∪ Ioi 0 := by
      ext t
      simp only [mem_Ici, mem_union, mem_singleton_iff, mem_Ioi]
      constructor
      · intro h
        rcases h.eq_or_lt with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (h | h)
        · exact h.ge
        · exact h.le
    have := measureReal_union (μ := (μ : Measure ℝ)) (s₁ := {0}) (s₂ := Ioi 0)
      (by simp) measurableSet_Ioi
    rw [← hu, h0, zero_add] at this
    rw [this]
    simp
  rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun k => (continuous_rampF _ _).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ fun t => ?_) (ae_of_all _ fun t => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (rampF_nonneg _ _ _)]
    exact rampF_le_one _ _ _
  · by_cases ht : 0 ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
      refine tendsto_const_nhds.congr fun k => ?_
      unfold rampF
      have : 1 ≤ (k : ℝ) * t + 1 := by
        have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) ht
        linarith
      rw [min_eq_left this, max_eq_right zero_le_one]
    · rw [indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht)]
      have ht' : t < 0 := not_le.mp ht
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / -t)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      have h1 : 1 / -t ≤ k := hK.trans (by exact_mod_cast hk)
      have h2 : 1 ≤ (k : ℝ) * -t := by rwa [div_le_iff₀ (by linarith)] at h1
      unfold rampF
      refine (max_eq_left (min_le_of_right_le ?_)).symm
      linarith

theorem intervalIntegrable_posInd {φ : ℝ → ℝ} (hφ : Measurable φ) (u v : ℝ) :
    IntervalIntegrable (fun y => posInd (φ y)) volume u v := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp)
    (measurable_posInd.comp hφ).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  unfold posInd
  rw [Real.norm_eq_abs]
  by_cases ht : 0 < φ y
  · rw [indicator_of_mem (show φ y ∈ Ioi (0 : ℝ) from ht)]
    simp
  · rw [indicator_of_notMem (show φ y ∉ Ioi (0 : ℝ) from ht)]
    simp

/-- **From the limiting distribution to the density**: the boundary `{0}` has measure zero. -/
theorem tendsto_posInd_of_limiting {φ : ℝ → ℝ} (hφ : Measurable φ) {μ : ProbabilityMeasure ℝ}
    (h : HasLimitingDistribution φ μ) (h0 : (μ : Measure ℝ).real {0} = 0) :
    Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, posInd (φ y)) atTop
      (𝓝 ((μ : Measure ℝ).real (Ioi 0))) := by
  have hint := fun Y => intervalIntegrable_posInd hφ 0 Y
  rw [tendsto_order]
  constructor
  · intro L hL
    obtain ⟨k, hk⟩ := ((tendsto_order.mp (tendsto_integral_ramp μ)).1 L hL).exists
    have hlim := h (rampB k 0)
    filter_upwards [(tendsto_order.mp hlim).1 L hk, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
    refine lt_of_lt_of_le hY (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine intervalIntegral.integral_mono_on hY0.le
      (intervalIntegrable_comp_bcf hφ (rampB k 0) 0 Y) (hint Y) fun y _ => ?_
    exact rampF_zero_le_posInd (by positivity) _
  · intro L hL
    obtain ⟨k, hk⟩ := ((tendsto_order.mp (tendsto_integral_ramp_one μ h0)).2 L hL).exists
    have hlim := h (rampB k 1)
    filter_upwards [(tendsto_order.mp hlim).2 L hk, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (by positivity)) hY
    refine intervalIntegral.integral_mono_on hY0.le (hint Y)
      (intervalIntegrable_comp_bcf hφ (rampB k 1) 0 Y) fun y _ => ?_
    exact posInd_le_rampF_one (by positivity) _

/-- The sign of `φ` is that of the race. -/
theorem posInd_phiA {a y : ℝ} (hy : log 2 ≤ y) :
    posInd (phiA a y) = if li ((exp y) ^ (a + 1)) < thetaPow a (exp y) then 1 else 0 := by
  have hy0 : 0 < y := (log_pos (by norm_num)).trans_le hy
  have hw : 0 < log (exp y) / (exp y) ^ (a + 1 / 2) := by
    rw [log_exp]
    exact div_pos hy0 (rpow_pos_of_pos (exp_pos y) _)
  have hφ : phiA a y = (thetaPow a (exp y) - li ((exp y) ^ (a + 1))) *
      (log (exp y) / (exp y) ^ (a + 1 / 2)) := if_pos hy
  have hiff : 0 < phiA a y ↔ li ((exp y) ^ (a + 1)) < thetaPow a (exp y) := by
    rw [hφ, mul_pos_iff_of_pos_right hw, sub_pos]
  unfold posInd
  by_cases h : li ((exp y) ^ (a + 1)) < thetaPow a (exp y)
  · rw [if_pos h, indicator_of_mem (show phiA a y ∈ Ioi (0 : ℝ) from hiff.mpr h)]
  · rw [if_neg h, indicator_of_notMem (show phiA a y ∉ Ioi (0 : ℝ) from fun h' => h (hiff.mp h'))]

/-- The substitution `x = e^y`. -/
theorem integral_indicator_eq {a : ℝ} (ha : -1 < a) {X : ℝ} (hX : 2 ≤ X) :
    ∫ x in (2 : ℝ)..X, ({x : ℝ | li (x ^ (a + 1)) < thetaPow a x}).indicator (fun x => 1 / x) x =
      ∫ y in (0 : ℝ)..log X, posInd (phiA a y) := by
  set S := {x : ℝ | li (x ^ (a + 1)) < thetaPow a x} with hS
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl : log 2 ≤ log X := log_le_log (by norm_num) hX
  have himg : exp '' Ioc (log 2) (log X) = Ioc 2 X := by
    ext x
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      constructor
      · rwa [← log_lt_iff_lt_exp (by norm_num)]
      · rwa [← le_log_iff_exp_le (by linarith)]
    · rintro ⟨h1, h2⟩
      have hx : 0 < x := by linarith
      exact ⟨log x, ⟨log_lt_log (by norm_num) h1, log_le_log hx h2⟩, exp_log hx⟩
  rw [intervalIntegral.integral_of_le hX, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
      (fun y _ => (hasDerivAt_exp y).hasDerivWithinAt) exp_injective.injOn]
  have hsplit : ∫ y in (0 : ℝ)..log X, posInd (phiA a y) =
      ∫ y in log 2..log X, posInd (phiA a y) := by
    have hm := measurable_phiA ha
    rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_posInd hm 0 (log 2))
      (intervalIntegrable_posInd hm (log 2) (log X))]
    have hz : ∫ y in (0 : ℝ)..log 2, posInd (phiA a y) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ log 2 := by simp [ae_iff]
      filter_upwards [hne] with y hy hmem
      rw [uIoc_of_le hl2.le] at hmem
      have hlt : y < log 2 := lt_of_le_of_ne hmem.2 hy
      have : phiA a y = 0 := if_neg (not_le.mpr hlt)
      rw [this]
      simp [posInd]
    rw [hz, zero_add]
  rw [hsplit, intervalIntegral.integral_of_le hl]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  rw [posInd_phiA hy.1.le, abs_of_pos (exp_pos y), smul_eq_mul]
  by_cases h : li ((exp y) ^ (a + 1)) < thetaPow a (exp y)
  · rw [if_pos h, indicator_of_mem (show exp y ∈ S from h)]
    field_simp
  · rw [if_neg h, indicator_of_notMem (show exp y ∉ S from h), mul_zero]

/-- **Theorem 3(ii)** (Bias law). Assume RH and LI. For every real `a > −½`, the limiting
distribution `μ_a` of `E_a(e^y)` is absolutely continuous and symmetric about `−1/(2a+1)`, and the
logarithmic density of `{x : θ_a(x) > li(x^{a+1})}` exists and equals
`δ_a = ½ − (1/π) ∫_0^∞ sin(ξ/(2a+1))/ξ · Π_{γ>0} J₀(2ξ/|½+a+iγ|) dξ`; the product converges and the
integrand is integrable. -/
theorem theorem3_ii (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI)
    {a : ℝ} (ha : -1 / 2 < a) {μ : ProbabilityMeasure ℝ}
    (hμ : HasLimitingDistribution (phiA a) μ) :
    (μ : Measure ℝ) ≪ volume ∧
    (μ : Measure ℝ).map (fun t => 2 * (-1 / (2 * a + 1)) - t) = μ ∧
    (∀ ξ : ℝ, Multipliable (fun γ : zeroOrdinates => besselJ0 (2 * ξ / zeroDen a γ))) ∧
    IntegrableOn (fun ξ => sin (ξ / (2 * a + 1)) / ξ * prodJ a ξ) (Ioi 0) ∧
    HasLogDensity {x : ℝ | li (x ^ (a + 1)) < thetaPow a x} (deltaA a) := by
  have hac := absCont_limiting hE hN hK h19 hB hRS hRH hLI ha hμ
  refine ⟨hac, symm_limiting hE hN hK h19 hRH hLI ha hμ, multipliable_prodJ hN hRH a, ?_, ?_⟩
  · have h := integrableOn_sin (integrable_charFun_shiftLaw hE hN hK h19 hB hRH hLI ha hμ)
      (1 / (2 * a + 1))
    refine h.congr_fun (fun ξ _ => ?_) measurableSet_Ioi
    simp only
    rw [charFun_shiftLaw hE hN hK h19 hRH hLI ha hμ, Complex.ofReal_re]
    congr 3
    ring
  · have ha1 : -1 < a := by linarith
    have h0 : (μ : Measure ℝ).real {0} = 0 := by
      simp only [Measure.real, hac (by simp : volume ({0} : Set ℝ) = 0)]
      rfl
    have hd := tendsto_posInd_of_limiting (measurable_phiA ha1) hμ h0
    rw [deltaA_eq hE hN hK h19 hB hRS hRH hLI ha hμ] at hd
    unfold HasLogDensity
    refine (hd.comp tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    simp only [Function.comp_apply]
    rw [integral_indicator_eq ha1 hX]

end CpsLean
