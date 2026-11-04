module

public import CpsLean.Classical.RubinsteinSarnakInversion
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false

/-!
# Symmetric laws with integrable characteristic function

Consequences of the inversion formula, for a probability measure `ν` on `ℝ`, symmetric about `0`,
with integrable characteristic function:

* `real_Ioi_zero`, `real_singleton_zero`: `ν(0, ∞) = ½` and `ν{0} = 0`;
* `real_Ioc_le`: `ν(u, v] ≤ M (v − u)`, with `M = (1/π) ∫_0^∞ |ν̂|`;
* `absCont_of_integrable_charFun`: `ν` is absolutely continuous.
-/

open Real MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace CpsLean

variable (ν : ProbabilityMeasure ℝ)

/-- `M = (1/π) ∫_0^∞ |ν̂|`. -/
noncomputable def invConst : ℝ := 1 / π * ∫ ξ in Ioi (0 : ℝ), |(charFun (ν : Measure ℝ) ξ).re|

theorem invConst_nonneg : 0 ≤ invConst ν :=
  mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _)

variable {ν}

theorem integrableOn_re (hint : Integrable (charFun (ν : Measure ℝ))) :
    IntegrableOn (fun ξ => |(charFun (ν : Measure ℝ) ξ).re|) (Ioi 0) :=
  (hint.re.abs).integrableOn

/-- `|sin(pξ)/ξ| ≤ |p|` for `ξ > 0`. -/
theorem abs_sin_div_le (p : ℝ) {ξ : ℝ} (hξ : 0 < ξ) : |sin (p * ξ) / ξ| ≤ |p| := by
  rw [abs_div, abs_of_pos hξ, div_le_iff₀ hξ]
  calc |sin (p * ξ)| ≤ |p * ξ| := abs_sin_le_abs
    _ = |p| * ξ := by rw [abs_mul, abs_of_pos hξ]

theorem integrableOn_sin (hint : Integrable (charFun (ν : Measure ℝ))) (p : ℝ) :
    IntegrableOn (fun ξ => sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_re hint).const_mul |p|) ?_ ?_
  · have hm : Measurable fun ξ : ℝ => (charFun (ν : Measure ℝ) ξ).re :=
      Complex.measurable_re.comp measurable_charFun
    exact (((measurable_sin.comp (measurable_const.mul measurable_id)).div measurable_id).mul
      hm).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ξ hξ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_sin_div_le p hξ) (abs_nonneg _)

/-- `|ν(p, ∞) − ½| ≤ M p`. -/
theorem abs_real_Ioi_sub_half_le (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ)))
    {p : ℝ} (hp : 0 < p) : |(ν : Measure ℝ).real (Ioi p) - 1 / 2| ≤ invConst ν * p := by
  rw [hRS ν hsym hint p hp]
  have h : ‖∫ ξ in Ioi (0 : ℝ), sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re‖ ≤
      ∫ ξ in Ioi (0 : ℝ), p * |(charFun (ν : Measure ℝ) ξ).re| := by
    refine norm_integral_le_of_norm_le ((integrableOn_re hint).const_mul p) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ξ hξ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := abs_sin_div_le p hξ
    rw [abs_of_pos hp] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  have e : (1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re)
      - 1 / 2 = -(1 / π * ∫ ξ in Ioi (0 : ℝ), sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re) := by
    ring
  rw [e, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  unfold invConst
  calc 1 / π * _ ≤ 1 / π * (p * ∫ ξ in Ioi (0 : ℝ), |(charFun (ν : Measure ℝ) ξ).re|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- `ν(p, ∞) − ν(q, ∞) ≤ M (q − p)` for `0 < p ≤ q`. -/
theorem real_Ioi_sub_le (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ)))
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (ν : Measure ℝ).real (Ioi p) - (ν : Measure ℝ).real (Ioi q) ≤ invConst ν * (q - p) := by
  rw [hRS ν hsym hint p hp, hRS ν hsym hint q (hp.trans_le hpq)]
  have hd : (1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re) -
      (1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (q * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re) =
      1 / π * ∫ ξ in Ioi (0 : ℝ), (sin (q * ξ) - sin (p * ξ)) / ξ * (charFun (ν : Measure ℝ) ξ).re := by
    have : ∫ ξ in Ioi (0 : ℝ), (sin (q * ξ) - sin (p * ξ)) / ξ * (charFun (ν : Measure ℝ) ξ).re =
        (∫ ξ in Ioi (0 : ℝ), sin (q * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re) -
          ∫ ξ in Ioi (0 : ℝ), sin (p * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re := by
      rw [← integral_sub (integrableOn_sin hint q) (integrableOn_sin hint p)]
      congr 1
      funext ξ
      ring
    rw [this]
    ring
  rw [hd]
  have h : ‖∫ ξ in Ioi (0 : ℝ), (sin (q * ξ) - sin (p * ξ)) / ξ * (charFun (ν : Measure ℝ) ξ).re‖ ≤
      ∫ ξ in Ioi (0 : ℝ), (q - p) * |(charFun (ν : Measure ℝ) ξ).re| := by
    refine norm_integral_le_of_norm_le ((integrableOn_re hint).const_mul (q - p)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ξ hξ => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hξ0 : (0 : ℝ) < ξ := hξ
    rw [abs_div, abs_of_pos hξ0, div_le_iff₀ hξ0]
    calc |sin (q * ξ) - sin (p * ξ)| ≤ |q * ξ - p * ξ| := abs_sin_sub_sin_le _ _
      _ = (q - p) * ξ := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hpq), abs_of_pos hξ0]
  rw [integral_const_mul, Real.norm_eq_abs] at h
  unfold invConst
  calc 1 / π * _ ≤ 1 / π * |∫ ξ in Ioi (0 : ℝ), (sin (q * ξ) - sin (p * ξ)) / ξ *
          (charFun (ν : Measure ℝ) ξ).re| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ 1 / π * ((q - p) * ∫ ξ in Ioi (0 : ℝ), |(charFun (ν : Measure ℝ) ξ).re|) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- By symmetry `ν(s) = ν(−s)`. -/
theorem real_preimage_neg (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (ν : Measure ℝ).real ((fun t : ℝ => -t) ⁻¹' s) = (ν : Measure ℝ).real s := by
  have h : ((ν : Measure ℝ).map (fun t => -t)).real s = (ν : Measure ℝ).real s := by rw [hsym]
  rw [map_measureReal_apply measurable_neg hs] at h
  exact h

/-- `ν(0, ∞) ≥ ν(p, ∞) ≥ ½ − M p` for every `p > 0`, hence `ν(0, ∞) ≥ ½`. -/
theorem half_le_real_Ioi_zero (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ))) :
    1 / 2 ≤ (ν : Measure ℝ).real (Ioi 0) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set M := invConst ν
  have hM : 0 ≤ M := invConst_nonneg ν
  set p := ε / (M + 1) with hp
  have hp0 : 0 < p := by positivity
  have h1 := abs_real_Ioi_sub_half_le hRS hsym hint hp0
  have h2 : (ν : Measure ℝ).real (Ioi p) ≤ (ν : Measure ℝ).real (Ioi 0) :=
    measureReal_mono (Ioi_subset_Ioi hp0.le)
  have h3 : M * p ≤ ε := by
    rw [hp, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have := (abs_le.mp h1).1
  linarith

/-- `ν{0} = 0` and `ν(0, ∞) = ½`. -/
theorem real_singleton_zero_and (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ))) :
    (ν : Measure ℝ).real {0} = 0 ∧ (ν : Measure ℝ).real (Ioi 0) = 1 / 2 := by
  have h := half_le_real_Ioi_zero hRS hsym hint
  have hneg : (ν : Measure ℝ).real (Iio 0) = (ν : Measure ℝ).real (Ioi 0) := by
    rw [← real_preimage_neg hsym measurableSet_Ioi]
    congr 1
    ext t
    simp
  have htot : (ν : Measure ℝ).real (Iio 0) + (ν : Measure ℝ).real {0} +
      (ν : Measure ℝ).real (Ioi 0) = 1 := by
    have hu : (univ : Set ℝ) = (Iio 0 ∪ {0}) ∪ Ioi 0 := by
      ext t
      simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]
      rcases lt_trichotomy t 0 with h | h | h <;> tauto
    have h1 : (ν : Measure ℝ).real (Iio 0 ∪ {0}) =
        (ν : Measure ℝ).real (Iio 0) + (ν : Measure ℝ).real {0} :=
      measureReal_union (by simp) (measurableSet_singleton _)
    have h2 : (ν : Measure ℝ).real ((Iio 0 ∪ {0}) ∪ Ioi 0) =
        (ν : Measure ℝ).real (Iio 0 ∪ {0}) + (ν : Measure ℝ).real (Ioi 0) :=
      measureReal_union (by
        rw [Set.disjoint_left]
        rintro t (ht | ht) ht2
        · exact absurd ht2 (not_lt.mpr (le_of_lt ht))
        · rw [mem_singleton_iff] at ht
          rw [ht] at ht2
          exact lt_irrefl _ ht2) measurableSet_Ioi
    rw [← h1, ← h2, ← hu]
    simp
  have h0 : 0 ≤ (ν : Measure ℝ).real {0} := measureReal_nonneg
  constructor <;> linarith

/-- `ν(p, q] = ν(p, ∞) − ν(q, ∞)`. -/
theorem real_Ioc_eq {p q : ℝ} (hpq : p ≤ q) :
    (ν : Measure ℝ).real (Ioc p q) =
      (ν : Measure ℝ).real (Ioi p) - (ν : Measure ℝ).real (Ioi q) := by
  have hu : Ioi p = Ioc p q ∪ Ioi q := (Ioc_union_Ioi_eq_Ioi hpq).symm
  have := measureReal_union (μ := (ν : Measure ℝ)) (s₁ := Ioc p q) (s₂ := Ioi q) (by
    rw [Set.disjoint_left]
    exact fun t ht ht2 => absurd ht.2 (not_le.mpr ht2)) measurableSet_Ioi
  rw [← hu] at this
  linarith

/-- `ν(p, q] ≤ M (q − p)` for `0 ≤ p ≤ q`. -/
theorem real_Ioc_nonneg_le (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ)))
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (ν : Measure ℝ).real (Ioc p q) ≤ invConst ν * (q - p) := by
  rw [real_Ioc_eq hpq]
  rcases hp.eq_or_lt with rfl | hp0
  · rcases hpq.eq_or_lt with rfl | hq
    · simp
    · have h1 := abs_real_Ioi_sub_half_le hRS hsym hint hq
      have h2 := (real_singleton_zero_and hRS hsym hint).2
      have := (abs_le.mp h1).1
      rw [h2, sub_zero]
      linarith
  · exact real_Ioi_sub_le hRS hsym hint hp0 hpq

/-- `ν{x} = 0` for `x ≥ 0`. -/
theorem real_singleton_nonneg (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ)))
    {x : ℝ} (hx : 0 ≤ x) : (ν : Measure ℝ).real {x} = 0 := by
  rcases hx.eq_or_lt with rfl | hx0
  · exact (real_singleton_zero_and hRS hsym hint).1
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) measureReal_nonneg
  set M := invConst ν
  have hM : 0 ≤ M := invConst_nonneg ν
  set η := min (x / 2) (ε / (M + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηx : η ≤ x / 2 := min_le_left _ _
  have hηe : η ≤ ε / (M + 1) := min_le_right _ _
  have hsub : ({x} : Set ℝ) ⊆ Ioc (x - η) x := by
    rintro _ rfl
    exact ⟨by linarith, le_rfl⟩
  have h1 := real_Ioc_nonneg_le hRS hsym hint (p := x - η) (q := x) (by linarith) (by linarith)
  have h2 : (ν : Measure ℝ).real {x} ≤ (ν : Measure ℝ).real (Ioc (x - η) x) := measureReal_mono hsub
  have h3 : M * η ≤ ε := by
    have : η * (M + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp hηe
    nlinarith
  have e : x - (x - η) = η := by ring
  rw [e] at h1
  linarith

/-- `ν(u, v] ≤ M (v − u)` for `u ≤ v`. -/
theorem real_Ioc_le (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ)))
    {u v : ℝ} (huv : u ≤ v) : (ν : Measure ℝ).real (Ioc u v) ≤ invConst ν * (v - u) := by
  set M := invConst ν
  have hM : 0 ≤ M := invConst_nonneg ν
  -- the case `v ≤ 0`
  have hneg : ∀ {u v : ℝ}, u ≤ v → v ≤ 0 → (ν : Measure ℝ).real (Ioc u v) ≤ M * (v - u) := by
    intro u v huv hv
    rw [← real_preimage_neg hsym measurableSet_Ioc]
    have hpre : (fun t : ℝ => -t) ⁻¹' Ioc u v = Ico (-v) (-u) := by
      ext t
      simp only [mem_preimage, mem_Ioc, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    rw [hpre]
    have hsub : Ico (-v) (-u) ⊆ {-v} ∪ Ioc (-v) (-u) := by
      intro t ht
      rcases ht.1.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨h, ht.2.le⟩
    have h1 : (ν : Measure ℝ).real (Ico (-v) (-u)) ≤
        (ν : Measure ℝ).real {-v} + (ν : Measure ℝ).real (Ioc (-v) (-u)) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    rw [real_singleton_nonneg hRS hsym hint (by linarith), zero_add] at h1
    have h2 := real_Ioc_nonneg_le hRS hsym hint (p := -v) (q := -u) (by linarith) (by linarith)
    have e : -u - -v = v - u := by ring
    rw [e] at h2
    linarith
  rcases le_or_gt v 0 with hv | hv
  · exact hneg huv hv
  rcases le_or_gt 0 u with hu | hu
  · exact real_Ioc_nonneg_le hRS hsym hint hu huv
  · have hsub : Ioc u v = Ioc u 0 ∪ Ioc 0 v := (Ioc_union_Ioc_eq_Ioc hu.le hv.le).symm
    rw [hsub]
    have h1 := hneg hu.le le_rfl
    have h2 := real_Ioc_nonneg_le hRS hsym hint le_rfl hv.le
    have := measureReal_union_le (μ := (ν : Measure ℝ)) (Ioc u 0) (Ioc 0 v)
    nlinarith

/-- A probability measure with `ν(u, v] ≤ M (v − u)` is absolutely continuous. -/
theorem absCont_of_Ioc_le {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ {u v : ℝ}, u ≤ v → (ν : Measure ℝ).real (Ioc u v) ≤ M * (v - u)) :
    (ν : Measure ℝ) ≪ volume := by
  have hdiff : ∀ {u v : ℝ}, u ≤ v → cdf (ν : Measure ℝ) v - cdf (ν : Measure ℝ) u =
      (ν : Measure ℝ).real (Ioc u v) := by
    intro u v huv
    rw [cdf_eq_real, cdf_eq_real]
    have hu : Iic v = Iic u ∪ Ioc u v := (Iic_union_Ioc_eq_Iic huv).symm
    have := measureReal_union (μ := (ν : Measure ℝ)) (s₁ := Iic u) (s₂ := Ioc u v) (by
      rw [Set.disjoint_left]
      exact fun t ht ht2 => absurd ht2.1 (not_lt.mpr ht)) measurableSet_Ioc
    rw [← hu] at this
    linarith
  let S : StieltjesFunction ℝ :=
    { toFun := fun x => M * x - cdf (ν : Measure ℝ) x
      mono' := by
        intro u v huv
        have := h huv
        rw [← hdiff huv] at this
        simp only
        nlinarith
      right_continuous' := by
        intro x
        exact (continuousWithinAt_const.mul continuousWithinAt_id).sub
          ((cdf (ν : Measure ℝ)).right_continuous x) }
  have hS : ∀ x, S x = M * x - cdf (ν : Measure ℝ) x := fun _ => rfl
  have heq : (ν : Measure ℝ) + S.measure = ENNReal.ofReal M • (volume : Measure ℝ) := by
    refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
    · rw [Measure.add_apply]
      simp [StieltjesFunction.measure_Ioc]
    · rw [Measure.add_apply, StieltjesFunction.measure_Ioc, Measure.smul_apply, Real.volume_Ioc,
        hS, hS, smul_eq_mul, ← ENNReal.ofReal_mul hM]
      have hd := hdiff hab.le
      have hb := h hab.le
      have e : M * b - cdf (ν : Measure ℝ) b - (M * a - cdf (ν : Measure ℝ) a) =
          M * (b - a) - (ν : Measure ℝ).real (Ioc a b) := by
        rw [← hd]
        ring
      rw [e, ← ofReal_measureReal (s := Ioc a b),
        ← ENNReal.ofReal_add measureReal_nonneg (sub_nonneg.mpr hb)]
      congr 1
      ring
  refine Measure.AbsolutelyContinuous.mk fun s _ hs => ?_
  have : (ν : Measure ℝ) s ≤ ((ν : Measure ℝ) + S.measure) s := by
    rw [Measure.add_apply]
    exact le_self_add
  rw [heq, Measure.smul_apply, hs, smul_zero] at this
  exact le_antisymm this bot_le

/-- **Absolute continuity.** A symmetric law with integrable characteristic function is absolutely
continuous. -/
theorem absCont_of_integrable_charFun (hRS : RubinsteinSarnakInversion)
    (hsym : (ν : Measure ℝ).map (fun t => -t) = ν) (hint : Integrable (charFun (ν : Measure ℝ))) :
    (ν : Measure ℝ) ≪ volume :=
  absCont_of_Ioc_le (invConst_nonneg ν) (real_Ioc_le hRS hsym hint)

end CpsLean
