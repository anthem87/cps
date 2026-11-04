module

public import CpsLean.Variance
public import CpsLean.Classical.AnsCor13a
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Distributions.Gaussian.CharFun
set_option autoImplicit false

/-!
# Theorem 4(a): the bias fades as the weight grows

* `abs_prodJ_sub_exp_le`: `|Π_γ J₀(2s/|½+a+iγ|) − e^{−s²σ_a²/2}| ≤ s⁴σ_a²/A²`.
* `theorem4_a`: **Theorem 4(a)**, `δ_a → ½` as `a → ∞`.

The characteristic function of the normalized symmetric part of `μ_a` is
`Π_γ J₀(ρ_γ ξ/σ_a)`, which tends to `e^{−ξ²/2}`; Lévy's continuity theorem gives the convergence in
law to `N(0, 1)`.
-/

open Real Filter Topology MeasureTheory Set ProbabilityTheory Finset

@[expose] public section

namespace CpsLean

/-- `|Π f_i − Π g_i| ≤ Σ |f_i − g_i|`, for factors of size at most `1`. -/
theorem abs_prod_sub_prod_le (f g : ℕ → ℝ) (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) (N : ℕ) :
    |∏ i ∈ range N, f i - ∏ i ∈ range N, g i| ≤ ∑ i ∈ range N, |f i - g i| := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [prod_range_succ, prod_range_succ, sum_range_succ]
    have hG : |∏ i ∈ range N, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => hg i
    have e : (∏ i ∈ range N, f i) * f N - (∏ i ∈ range N, g i) * g N =
        (∏ i ∈ range N, f i - ∏ i ∈ range N, g i) * f N +
          (∏ i ∈ range N, g i) * (f N - g N) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hf N)).trans ih
    · rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hG

/-- The sum `σ_a²`, over the enumeration. -/
theorem sigmaSq_eq_tsum {lam : ℕ → ℝ} (hmono : StrictMono lam)
    (hrange : Set.range lam = zeroOrdinates) (a : ℝ) :
    sigmaSq a = ∑' n, 2 / zeroDen a (lam n) ^ 2 :=
  ((ordEquiv hmono hrange).tsum_eq (fun γ : zeroOrdinates => 2 / zeroDen a γ ^ 2)).symm

theorem summable_two_div {lam : ℕ → ℝ} (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) (a : ℝ) :
    Summable fun n => 2 / zeroDen a (lam n) ^ 2 := by
  refine ((summable_inv_zeroDen hN hRH a hmono hrange).mul_left 2).congr fun n => ?_
  ring

theorem sigmaSq_pos (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a : ℝ) : 0 < sigmaSq a := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  rw [sigmaSq_eq_tsum hmono hrange]
  have hd : ∀ n, 0 < zeroDen a (lam n) := fun n => zeroDen_pos a (hpos n)
  exact (summable_two_div hN hRH hmono hrange a).tsum_pos (fun n => by have := hd n; positivity) 0
    (by have := hd 0; positivity)

/-- `|P_a(s) − e^{−s²σ_a²/2}| ≤ s⁴σ_a²/A²`, with `A = a + ½ ≠ 0`. -/
theorem abs_prodJ_sub_exp_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) {a : ℝ}
    (hA : a + 1 / 2 ≠ 0) (s : ℝ) :
    |prodJ a s - exp (-(s ^ 2 * sigmaSq a / 2))| ≤ s ^ 4 * sigmaSq a / (a + 1 / 2) ^ 2 := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  set A := a + 1 / 2 with hAdef
  have hA2 : 0 < A ^ 2 := by positivity
  set x : ℕ → ℝ := fun n => 2 * s / zeroDen a (lam n) with hx
  have hd : ∀ n, 0 < zeroDen a (lam n) := fun n => zeroDen_pos a (hpos n)
  have hsum := summable_two_div hN hRH hmono hrange a
  have hx2 : ∀ n, x n ^ 2 = 2 * s ^ 2 * (2 / zeroDen a (lam n) ^ 2) := fun n => by
    simp only [hx]
    rw [div_pow]
    ring
  -- the exponential side
  have hEsum : Tendsto (fun N => ∑ n ∈ range N, x n ^ 2 / 4) atTop (𝓝 (s ^ 2 * sigmaSq a / 2)) := by
    have hs : HasSum (fun n => x n ^ 2 / 4) (s ^ 2 * sigmaSq a / 2) := by
      have := (hsum.hasSum.mul_left (s ^ 2 / 2))
      rw [← sigmaSq_eq_tsum hmono hrange] at this
      convert this using 1
      · funext n
        rw [hx2]
        ring
      · ring
    exact hs.tendsto_sum_nat
  have hEprod : Tendsto (fun N => ∏ n ∈ range N, exp (-(x n ^ 2 / 4))) atTop
      (𝓝 (exp (-(s ^ 2 * sigmaSq a / 2)))) := by
    have := (continuous_exp.tendsto _).comp hEsum.neg
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  have hlim := (tendsto_prod_prodJ hN hRH a s hmono hrange).sub hEprod
  refine le_of_tendsto hlim.abs (Eventually.of_forall fun N => ?_)
  have htele := abs_prod_sub_prod_le (fun n => besselJ0 (x n)) (fun n => exp (-(x n ^ 2 / 4)))
    (fun n => abs_besselJ0_le_one _)
    (fun n => by
      rw [abs_of_pos (exp_pos _)]
      exact exp_le_one_iff.mpr (by have := sq_nonneg (x n); linarith)) N
  refine htele.trans ?_
  have hterm : ∀ n, |besselJ0 (x n) - exp (-(x n ^ 2 / 4))| ≤
      s ^ 4 / A ^ 2 * (2 / zeroDen a (lam n) ^ 2) := fun n => by
    refine (abs_besselJ0_sub_exp_le _).trans ?_
    have hden : A ^ 2 ≤ zeroDen a (lam n) ^ 2 := by
      rw [zeroDen_sq, hAdef]
      nlinarith [sq_nonneg (lam n)]
    have hdn := hd n
    have hle : x n ^ 2 ≤ 4 * s ^ 2 / A ^ 2 := by
      simp only [hx]
      rw [div_pow, mul_pow]
      norm_num
      exact div_le_div_of_nonneg_left (by positivity) hA2 hden
    have h4 : x n ^ 4 = x n ^ 2 * x n ^ 2 := by ring
    rw [h4, hx2 n]
    have hq : 0 ≤ 2 * s ^ 2 * (2 / zeroDen a (lam n) ^ 2) := by positivity
    rw [hx2 n] at hle
    calc 2 * s ^ 2 * (2 / zeroDen a (lam n) ^ 2) * (2 * s ^ 2 * (2 / zeroDen a (lam n) ^ 2)) / 8
        ≤ (4 * s ^ 2 / A ^ 2) * (2 * s ^ 2 * (2 / zeroDen a (lam n) ^ 2)) / 8 := by
          gcongr
      _ = _ := by
          field_simp
          ring
  calc ∑ n ∈ range N, |besselJ0 (x n) - exp (-(x n ^ 2 / 4))|
      ≤ ∑ n ∈ range N, s ^ 4 / A ^ 2 * (2 / zeroDen a (lam n) ^ 2) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = s ^ 4 / A ^ 2 * ∑ n ∈ range N, 2 / zeroDen a (lam n) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ s ^ 4 / A ^ 2 * sigmaSq a := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sigmaSq_eq_tsum hmono hrange]
        exact hsum.sum_le_tsum _ fun n _ => by have := hd n; positivity
    _ = _ := by
        ring

/-- `A² σ_a² → ∞`. -/
theorem tendsto_sq_mul_sigmaSq (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    Tendsto (fun a : ℝ => (a + 1 / 2) ^ 2 * sigmaSq a) atTop atTop := by
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hLt : Tendsto (fun a : ℝ => log ((a + 1 / 2) / (2 * π))) atTop atTop :=
    tendsto_log_atTop.comp (hAt.atTop_div_const (by positivity))
  have heq := (Asymptotics.IsEquivalent.refl (u := fun a : ℝ => (a + 1 / 2) ^ 2)).mul
    (sigmaSq_isEquivalent hN hRH hLI)
  refine Asymptotics.IsEquivalent.tendsto_atTop heq.symm ?_
  have hv : Tendsto (fun a : ℝ => (a + 1 / 2) * log ((a + 1 / 2) / (2 * π)) / 2) atTop atTop :=
    (hAt.atTop_mul_atTop₀ hLt).atTop_div_const (by norm_num)
  refine hv.congr' ?_
  filter_upwards [hAt.eventually_gt_atTop 0] with a ha
  simp only [Pi.mul_apply]
  field_simp

/-- A limiting distribution exists. -/
theorem exists_limiting (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hC : AnsCor13a) (hRH : RiemannHypothesis) {a : ℝ}
    (ha : -1 / 2 < a) : ∃ μ : ProbabilityMeasure ℝ, HasLimitingDistribution (phiA a) μ := by
  obtain ⟨lam, hmono, hpos, hrange, htop⟩ := exists_ordinate_enum hN
  exact hC _ _ _ _ _ (ansExpansion_phiA hE hN hK hRH ha hmono hpos hrange htop)
    (ansCond_coefA hN hRH a hmono hpos hrange)

/-- The law of `s t` under `ν`. -/
noncomputable def scaleLaw (ν : ProbabilityMeasure ℝ) (s : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(ν : Measure ℝ).map (s * ·), Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance⟩

theorem coe_scaleLaw (ν : ProbabilityMeasure ℝ) (s : ℝ) :
    ((scaleLaw ν s : ProbabilityMeasure ℝ) : Measure ℝ) = (ν : Measure ℝ).map (s * ·) := rfl

/-- The standard Gaussian. -/
noncomputable def stdGauss : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

theorem coe_stdGauss : ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal 0 1 := rfl

theorem charFun_stdGauss (ξ : ℝ) :
    charFun ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ) ξ = (exp (-(ξ ^ 2 / 2)) : ℝ) := by
  rw [coe_stdGauss, charFun_gaussianReal]
  push_cast
  congr 1
  simp

theorem symm_stdGauss :
    ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ).map (fun t => -t) = (stdGauss : ProbabilityMeasure ℝ) := by
  rw [coe_stdGauss, gaussianReal_map_neg, neg_zero]

theorem integrable_charFun_stdGauss :
    Integrable (charFun ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ)) := by
  have h : Integrable fun ξ : ℝ => exp (-(1 / 2) * ξ ^ 2) := integrable_exp_neg_mul_sq (by norm_num)
  refine h.ofReal.congr (ae_of_all _ fun ξ => ?_)
  simp only
  rw [charFun_stdGauss]
  congr 2
  ring

theorem stdGauss_frontier (ε : ℝ) : ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ) (frontier (Ioi ε)) = 0 := by
  rw [frontier_Ioi]
  exact gaussianReal_absolutelyContinuous 0 (by norm_num) (by simp)

/-- **Theorem 4(a).** Assume RH and LI. Then `δ_a → ½` as `a → ∞`. -/
theorem theorem4_a (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hC : AnsCor13a) (h19 : AnsThm19) (hB : BesselDecay)
    (hRS : RubinsteinSarnakInversion) (hRH : RiemannHypothesis) (hLI : LI) :
    Tendsto deltaA atTop (𝓝 (1 / 2)) := by
  refine tendsto_of_seq_tendsto fun x hx => ?_
  -- reduce to `a_n ≥ 1`
  set y : ℕ → ℝ := fun n => max (x n) 1 with hy
  have hyt : Tendsto y atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) hx
  have hxy : ∀ᶠ n in atTop, deltaA (y n) = (deltaA ∘ x) n := by
    filter_upwards [hx.eventually_ge_atTop 1] with n hn
    simp only [hy, Function.comp_apply, max_eq_left hn]
  refine Tendsto.congr' hxy ?_
  have hy1 : ∀ n, 1 ≤ y n := fun n => le_max_right _ _
  have hya : ∀ n, -1 / 2 < y n := fun n => by linarith [hy1 n]
  choose μ hμ using fun n => exists_limiting hE hN hK hC hRH (hya n)
  set b : ℕ → ℝ := fun n => 1 / (2 * y n + 1) with hb
  have hb0 : ∀ n, 0 < b n := fun n => by
    have := hy1 n
    simp only [hb]
    positivity
  set ν : ℕ → ProbabilityMeasure ℝ := fun n => shiftLaw (μ n) (b n) with hν
  set σ : ℕ → ℝ := fun n => √(sigmaSq (y n)) with hσ
  have hσsq : ∀ n, σ n ^ 2 = sigmaSq (y n) := fun n =>
    Real.sq_sqrt (sigmaSq_pos hN hRH _).le
  have hσ0 : ∀ n, 0 < σ n := fun n => Real.sqrt_pos.mpr (sigmaSq_pos hN hRH _)
  have hcharν : ∀ n ξ, charFun ((ν n : ProbabilityMeasure ℝ) : Measure ℝ) ξ = (prodJ (y n) ξ : ℂ) :=
    fun n ξ => charFun_shiftLaw hE hN hK h19 hRH hLI (hya n) (hμ n) ξ
  have hsymν : ∀ n, ((ν n : ProbabilityMeasure ℝ) : Measure ℝ).map (fun t => -t) = ν n :=
    fun n => symm_shiftLaw hE hN hK h19 hRH hLI (hya n) (hμ n)
  have hintν : ∀ n, Integrable (charFun ((ν n : ProbabilityMeasure ℝ) : Measure ℝ)) :=
    fun n => integrable_charFun_shiftLaw hE hN hK h19 hB hRH hLI (hya n) (hμ n)
  have hδ : ∀ n, deltaA (y n) = ((ν n : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi (b n)) := fun n => by
    rw [← deltaA_eq hE hN hK h19 hB hRS hRH hLI (hya n) (hμ n)]
    exact (real_shiftLaw_Ioi (μ n) (b n)).symm
  -- `A² σ² → ∞`
  have hAσ : Tendsto (fun n => (y n + 1 / 2) ^ 2 * sigmaSq (y n)) atTop atTop :=
    (tendsto_sq_mul_sigmaSq hN hRH hLI).comp hyt
  -- the normalized laws
  set τ : ℕ → ProbabilityMeasure ℝ := fun n => scaleLaw (ν n) (σ n)⁻¹ with hτ
  have hchar : ∀ ξ : ℝ, Tendsto (fun n => charFun ((τ n : ProbabilityMeasure ℝ) : Measure ℝ) ξ) atTop
      (𝓝 (charFun ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ) ξ)) := by
    intro ξ
    rw [charFun_stdGauss]
    have hval : ∀ n, charFun ((τ n : ProbabilityMeasure ℝ) : Measure ℝ) ξ =
        (prodJ (y n) ((σ n)⁻¹ * ξ) : ℂ) := fun n => by
      simp only [hτ]
      rw [coe_scaleLaw, charFun_map_mul, hcharν]
    simp_rw [hval]
    refine (Complex.continuous_ofReal.tendsto _).comp ?_
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
    have hbound : ∀ n, |prodJ (y n) ((σ n)⁻¹ * ξ) - exp (-(ξ ^ 2 / 2))| ≤
        ξ ^ 4 * ((y n + 1 / 2) ^ 2 * sigmaSq (y n))⁻¹ := fun n => by
      have hA : y n + 1 / 2 ≠ 0 := by linarith [hy1 n]
      have h := abs_prodJ_sub_exp_le hN hRH hA ((σ n)⁻¹ * ξ)
      have hsn := hσ0 n
      have e1 : ((σ n)⁻¹ * ξ) ^ 2 * sigmaSq (y n) / 2 = ξ ^ 2 / 2 := by
        rw [← hσsq n]
        field_simp
      rw [e1] at h
      refine h.trans (le_of_eq ?_)
      rw [← hσsq n]
      field_simp
    refine squeeze_zero (fun n => abs_nonneg _) hbound ?_
    have := (tendsto_inv_atTop_zero.comp hAσ).const_mul (ξ ^ 4)
    simpa using this
  have hweak : Tendsto τ atTop (𝓝 stdGauss) := ProbabilityMeasure.tendsto_of_tendsto_charFun hchar
  -- the bias, on the normalized scale
  have hδτ : ∀ n, ((ν n : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi (b n)) =
      ((τ n : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi (b n / σ n)) := fun n => by
    simp only [hτ]
    rw [coe_scaleLaw, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext t
    have hsn := hσ0 n
    simp only [Set.mem_Ioi, Set.mem_preimage]
    rw [div_lt_iff₀ hsn, inv_mul_eq_div, div_mul_cancel₀ _ hsn.ne']
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, b n / σ n < ε := by
    intro ε hε
    filter_upwards [hAσ.eventually_gt_atTop ((1 / (2 * ε)) ^ 2)] with n hn
    have hA : 0 < y n + 1 / 2 := by linarith [hy1 n]
    have hsn := hσ0 n
    rw [← hσsq n, ← mul_pow, sq_lt_sq₀ (by positivity) (by positivity)] at hn
    have hbn : b n = 1 / (2 * (y n + 1 / 2)) := by
      simp only [hb]
      congr 1
      ring
    rw [hbn, div_lt_iff₀ hsn, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  rw [tendsto_order]
  constructor
  · intro L hL
    -- choose `ε`
    set M := invConst stdGauss
    have hM : 0 ≤ M := invConst_nonneg stdGauss
    set ε := (1 / 2 - L) / (2 * (M + 1)) with hε
    have hε0 : 0 < ε := by
      have : 0 < 1 / 2 - L := by linarith
      positivity
    have hG := abs_real_Ioi_sub_half_le hRS symm_stdGauss integrable_charFun_stdGauss hε0
    have hG2 : L < ((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi ε) := by
      have h1 := (abs_le.mp hG).1
      have h2 : M * ε < 1 / 2 - L := by
        have h3 : ε * (2 * (M + 1)) = 1 / 2 - L := by
          rw [hε]
          field_simp
        nlinarith
      linarith
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
      (stdGauss_frontier ε)
    have hport2 : Tendsto (fun n => ((τ n : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi ε)) atTop
        (𝓝 (((stdGauss : ProbabilityMeasure ℝ) : Measure ℝ).real (Ioi ε))) :=
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
    filter_upwards [(tendsto_order.mp hport2).1 L hG2, hsmall ε hε0] with n h1 h2
    refine lt_of_lt_of_le h1 ?_
    rw [hδ, hδτ]
    exact measureReal_mono (Ioi_subset_Ioi h2.le)
  · intro L hL
    refine Eventually.of_forall fun n => ?_
    refine lt_of_le_of_lt ?_ hL
    rw [hδ, ← (real_singleton_zero_and hRS (hsymν n) (hintν n)).2]
    exact measureReal_mono (Ioi_subset_Ioi (hb0 n).le)

end CpsLean
