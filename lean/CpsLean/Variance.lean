module

public import CpsLean.BiasDensity
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
set_option autoImplicit false

/-!
# The variance `σ_a²` of the symmetric part of `μ_a`

* `sigmaSq a = σ_a² = Σ_{γ>0} 2/|½+a+iγ|² = ½ Σ_{γ>0} ρ_γ²`, with `ρ_γ = 2/|½+a+iγ|`.
* `sigmaSq_isEquivalent`: under RH and LI, `σ_a² ∼ log(A/2π)/(2A)` as `a → ∞`, `A = a + ½`.

The sum is written as `∫_0^∞ N(t) g_A(t) dt`, with `g_A(t) = 4t/(A²+t²)²`. The main term of `N(t)` is
then computed by the substitution `t = Au`.
-/

open Real Filter Topology MeasureTheory Set Asymptotics

@[expose] public section

namespace CpsLean

/-- `σ_a² = Σ_{γ>0} 2/|½+a+iγ|²`. -/
noncomputable def sigmaSq (a : ℝ) : ℝ := ∑' γ : zeroOrdinates, 2 / zeroDen a γ ^ 2

/-- `g_A(t) = 4t/(A²+t²)²`. -/
noncomputable def gA (A t : ℝ) : ℝ := 4 * t / (A ^ 2 + t ^ 2) ^ 2

/-- The main term of the Riemann–von Mangoldt formula. -/
noncomputable def rvmF (t : ℝ) : ℝ := t / (2 * π) * log (t / (2 * π)) - t / (2 * π)

theorem hasDerivAt_neg_f {A : ℝ} (hA : 0 < A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(2 / (A ^ 2 + s ^ 2))) (gA A t) t := by
  have hne : A ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => A ^ 2 + s ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add (A ^ 2)
  have h := ((hasDerivAt_const t (2 : ℝ)).div h1 hne).neg
  convert h using 1
  unfold gA
  field_simp
  ring

theorem gA_nonneg {A t : ℝ} (ht : 0 ≤ t) : 0 ≤ gA A t := by
  unfold gA
  positivity

theorem tendsto_neg_f {A : ℝ} (hA : 0 < A) :
    Tendsto (fun s : ℝ => -(2 / (A ^ 2 + s ^ 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => A ^ 2 + s ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
  have := (h1.const_div_atTop (2 : ℝ)).neg
  simpa using this

theorem integrableOn_gA {A l : ℝ} (hA : 0 < A) (hl : 0 ≤ l) : IntegrableOn (gA A) (Ioi l) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hasDerivAt_neg_f hA t)
    (fun t ht => gA_nonneg (hl.trans (le_of_lt ht))) (tendsto_neg_f hA)

theorem integral_gA {A l : ℝ} (hA : 0 < A) (hl : 0 ≤ l) :
    ∫ t in Ioi l, gA A t = 2 / (A ^ 2 + l ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hasDerivAt_neg_f hA t)
    (fun t ht => gA_nonneg (hl.trans (le_of_lt ht))) (tendsto_neg_f hA)]
  ring

section Enum

variable {lam : ℕ → ℝ}

/-- Under RH and LI, `N(t) = Σ_n 1[λ_n ≤ t]`. -/
theorem hasSum_zeroCount (hRH : RiemannHypothesis) (hLI : LI) (hmono : StrictMono lam)
    (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates) (t : ℝ) :
    HasSum (fun n => (Ici (lam n)).indicator (fun _ => (1 : ℝ)) t) (zeroCount t : ℝ) := by
  classical
  have hmem : ∀ n, lam n ∈ zeroOrdinates := fun n => hrange ▸ Set.mem_range_self n
  have hfin : {n : ℕ | lam n ≤ t}.Finite := by
    refine Set.Finite.of_finite_image (f := lam) ?_ hmono.injective.injOn
    refine (finite_ordinates_le t).subset ?_
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hmem n, hn⟩
  have hcount : zeroCount t = hfin.toFinset.card := by
    unfold zeroCount
    have hbij := finsum_mem_eq_of_bijOn (s := {n : ℕ | lam n ≤ t})
      (t := {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t})
      (f := fun _ => 1) (g := fun ρ => zeroMult ρ) (fun n => zeroOf (lam n)) ⟨?_, ?_, ?_⟩ ?_
    · rw [← hbij, finsum_mem_eq_finite_toFinset_sum _ hfin]
      simp
    · intro n hn
      exact ⟨zeroOf_mem hRH (hmem n), by simpa using hpos n, by simpa using hn⟩
    · intro n _ k _ h
      exact hmono.injective (by simpa using congrArg Complex.im h)
    · rintro ρ ⟨h0, h1, h2⟩
      have hγ : ρ.im ∈ zeroOrdinates := ⟨h1, ρ, h0, rfl⟩
      rw [← hrange] at hγ
      obtain ⟨n, hn⟩ := hγ
      refine ⟨n, ?_, ?_⟩
      · change lam n ≤ t
        rw [hn]
        exact h2
      · change zeroOf (lam n) = ρ
        rw [hn]
        exact (eq_zeroOf hRH h0).symm
    · intro n _
      exact (hLI.1 _ (zeroOf_mem hRH (hmem n)) (by simpa using hpos n)).symm
  have hsum : HasSum (fun n => (Ici (lam n)).indicator (fun _ => (1 : ℝ)) t)
      (∑ n ∈ hfin.toFinset, (Ici (lam n)).indicator (fun _ => (1 : ℝ)) t) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have : ¬ lam n ≤ t := by simpa using hn
      exact indicator_of_notMem (by simpa using this) _)
  have hval : ∑ n ∈ hfin.toFinset, (Ici (lam n)).indicator (fun _ => (1 : ℝ)) t = (zeroCount t : ℝ) := by
    rw [hcount, Finset.sum_congr rfl (g := fun _ => (1 : ℝ))]
    · simp
    · intro n hn
      have : lam n ≤ t := by simpa using hn
      exact indicator_of_mem (by simpa using this) _
  rwa [hval] at hsum

theorem monotone_zeroCount (hRH : RiemannHypothesis) (hLI : LI) (hmono : StrictMono lam)
    (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates) :
    Monotone (fun t : ℝ => (zeroCount t : ℝ)) := by
  intro s t hst
  refine hasSum_le (fun n => ?_) (hasSum_zeroCount hRH hLI hmono hpos hrange s)
    (hasSum_zeroCount hRH hLI hmono hpos hrange t)
  by_cases h : lam n ≤ s
  · rw [indicator_of_mem (show s ∈ Ici (lam n) from h),
      indicator_of_mem (show t ∈ Ici (lam n) from h.trans hst)]
  · rw [indicator_of_notMem (show s ∉ Ici (lam n) from h)]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

/-- **Abel summation.** `σ_a² = ∫_0^∞ N(t) g_A(t) dt`, `A = a + ½ > 0`. -/
theorem sigmaSq_eq_integral (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI)
    (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates)
    {a : ℝ} (ha : 0 < a + 1 / 2) :
    sigmaSq a = ∫ t in Ioi (0 : ℝ), (zeroCount t : ℝ) * gA (a + 1 / 2) t := by
  set A := a + 1 / 2 with hA
  set F : ℕ → ℝ → ℝ := fun n => (Ici (lam n)).indicator (gA A) with hF
  have hint : ∀ n, Integrable (F n) := fun n => by
    simp only [hF]
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_gA ha (hpos n).le
  have hval : ∀ n, ∫ t, F n t = 2 / zeroDen a (lam n) ^ 2 := fun n => by
    simp only [hF]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_gA ha (hpos n).le, zeroDen_sq]
  have hnorm : ∀ n, ∫ t, ‖F n t‖ = 2 / zeroDen a (lam n) ^ 2 := fun n => by
    rw [← hval n]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hF]
    by_cases h : t ∈ Ici (lam n)
    · rw [indicator_of_mem h, Real.norm_of_nonneg (gA_nonneg ((hpos n).le.trans h))]
    · rw [indicator_of_notMem h, norm_zero]
  have hs : Summable fun n => ∫ t, ‖F n t‖ := by
    simp_rw [hnorm]
    refine ((summable_inv_zeroDen hN hRH a hmono hrange).mul_left 2).congr fun n => ?_
    ring
  have hsum := hasSum_integral_of_summable_integral_norm hint hs
  simp_rw [hval] at hsum
  have htsum : ∀ t, ∑' n, F n t = (zeroCount t : ℝ) * gA A t := fun t => by
    have := (hasSum_zeroCount hRH hLI hmono hpos hrange t).mul_right (gA A t)
    rw [← this.tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hF]
    by_cases h : t ∈ Ici (lam n)
    · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  simp_rw [htsum] at hsum
  have hset : ∫ t in Ioi (0 : ℝ), (zeroCount t : ℝ) * gA A t = ∫ t, (zeroCount t : ℝ) * gA A t := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    have h0 : t ≤ 0 := not_lt.mp ht
    have hz := (hasSum_zeroCount hRH hLI hmono hpos hrange t)
    have : (zeroCount t : ℝ) = 0 := by
      refine hz.unique ?_
      convert hasSum_zero using 2 with n
      exact indicator_of_notMem (fun h : lam n ≤ t => absurd (hpos n) (not_lt.mpr (h.trans h0))) _
    rw [this, zero_mul]
  rw [hset, ← hsum.tsum_eq]
  unfold sigmaSq
  exact ((ordEquiv hmono hrange).tsum_eq (fun γ : zeroOrdinates => 2 / zeroDen a γ ^ 2)).symm

/-- `|N(t) − F(t)| ≤ C (1 + √t)` for every `t ≥ 0`. -/
theorem exists_zeroCount_sub_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI)
    (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → |(zeroCount t : ℝ) - rvmF t| ≤ C * (1 + √t) := by
  obtain ⟨C₀, hC₀⟩ := hN.bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hC₀.and (eventually_ge_atTop (1 : ℝ)))
  set T₁ := max T₀ 1 with hT₁
  have hcont : ContinuousOn rvmF (Set.Icc 0 T₁) := by
    have h : Continuous rvmF := by
      unfold rvmF
      exact ((Real.continuous_mul_log.comp (continuous_id.div_const _)).sub (continuous_id.div_const _))
    exact h.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set N₁ : ℝ := (zeroCount T₁ : ℝ) with hN₁
  refine ⟨N₁ + |B| + 2 * |C₀|, by positivity, fun t ht => ?_⟩
  have hs0 : 0 ≤ √t := Real.sqrt_nonneg t
  rcases le_or_gt t T₁ with h | h
  · have h1 : (zeroCount t : ℝ) ≤ N₁ := monotone_zeroCount hRH hLI hmono hpos hrange h
    have h2 := hB t ⟨ht, h⟩
    rw [Real.norm_eq_abs] at h2
    have h3 : (0 : ℝ) ≤ zeroCount t := Nat.cast_nonneg _
    have h4 := abs_sub (zeroCount t : ℝ) (rvmF t)
    rw [abs_of_nonneg h3] at h4
    have hN0 : 0 ≤ N₁ := Nat.cast_nonneg _
    have h5 : |B| ≥ B := le_abs_self B
    have hC0 := abs_nonneg C₀
    have hp : 0 ≤ (N₁ + |B| + 2 * |C₀|) * √t := by positivity
    nlinarith
  · obtain ⟨hb, h1⟩ := hT₀ t ((le_max_left _ _).trans h.le)
    have hl : 0 ≤ log t := log_nonneg h1
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hl] at hb
    have ht0 : 0 < t := by linarith
    have hl2 := log_le_two_sqrt ht0
    have hN0 : 0 ≤ N₁ := Nat.cast_nonneg _
    have hC0 := abs_nonneg C₀
    have hB0 := abs_nonneg B
    have h2 : C₀ * log t ≤ |C₀| * (2 * √t) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hl).trans
        (mul_le_mul_of_nonneg_left hl2 hC0)
    unfold rvmF
    calc _ ≤ C₀ * log t := hb
      _ ≤ |C₀| * (2 * √t) := h2
      _ ≤ _ := by nlinarith [mul_nonneg hN0 hs0, mul_nonneg hB0 hs0, mul_nonneg hC0 hs0]

end Enum

/-- `u²/(1+u²)²`. -/
noncomputable def b1 (u : ℝ) : ℝ := u ^ 2 / (1 + u ^ 2) ^ 2

/-- `u² log u/(1+u²)²`. -/
noncomputable def b2 (u : ℝ) : ℝ := u ^ 2 * log u / (1 + u ^ 2) ^ 2

/-- `(1+√u) u/(1+u²)²`. -/
noncomputable def b3 (u : ℝ) : ℝ := (1 + √u) * (u / (1 + u ^ 2) ^ 2)

theorem integrable_b1 : IntegrableOn b1 (Ioi 0) := by
  refine (integrable_inv_one_add_sq.mono' ?_ (ae_of_all _ fun u => ?_)).integrableOn
  · unfold b1
    exact (by fun_prop : Measurable fun u : ℝ => u ^ 2 / (1 + u ^ 2) ^ 2).aestronglyMeasurable
  · unfold b1
    have h : 0 < 1 + u ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have e : (1 + u ^ 2)⁻¹ * (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := by field_simp
    rw [e]
    linarith

/-- `∫_0^∞ u²/(1+u²)² du = π/4`. -/
theorem integral_b1 : ∫ u in Ioi (0 : ℝ), b1 u = π / 4 := by
  have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt
      (fun s : ℝ => (arctan s - s / (1 + s ^ 2)) / 2) (b1 u) u := by
    intro u _
    have hne : 1 + u ^ 2 ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * u) u := by
      simpa using ((hasDerivAt_id u).pow 2).const_add 1
    have h := ((hasDerivAt_arctan u).sub ((hasDerivAt_id u).div h1 hne)).div_const 2
    have h2 : HasDerivAt (fun s : ℝ => (arctan s - s / (1 + s ^ 2)) / 2) _ u := h
    refine h2.congr_deriv ?_
    unfold b1
    simp only [id]
    field_simp
    ring
  have hlim : Tendsto (fun s : ℝ => (arctan s - s / (1 + s ^ 2)) / 2) atTop (𝓝 (π / 4)) := by
    have h1 : Tendsto (fun s : ℝ => s / (1 + s ^ 2)) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ (tendsto_inv_atTop_zero (𝕜 := ℝ))
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
        positivity
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
        rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hs]
        nlinarith [sq_nonneg s]
    have h2 := ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).sub h1).div_const 2
    convert h2 using 2
    ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hd u hu) integrable_b1 hlim
  rw [this]
  simp

theorem integrable_b3 : IntegrableOn b3 (Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (3 / 2)).integrableOn) ?_ ?_
  · unfold b3
    exact (by fun_prop : Measurable fun u : ℝ => (1 + √u) * (u / (1 + u ^ 2) ^ 2)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    unfold b3
    have hp : 0 < 1 + u ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity), mul_div_assoc', div_le_iff₀ (by positivity)]
    have e : 3 / 2 * (1 + u ^ 2)⁻¹ * (1 + u ^ 2) ^ 2 = 3 / 2 * (1 + u ^ 2) := by field_simp
    rw [e]
    set s := √u with hs
    have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
    have hs0 : 0 ≤ s := Real.sqrt_nonneg u
    rw [← hs2]
    nlinarith [sq_nonneg (s ^ 2 - s), sq_nonneg (s ^ 2 - 1), sq_nonneg (s ^ 2 - 1 / 2)]

theorem integrable_b2 : IntegrableOn b2 (Ioi 0) := by
  have hm : Measurable b2 := by
    unfold b2
    fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1) (by simp) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu => ?_)
    obtain ⟨h0, h1⟩ := hu
    unfold b2
    have hp : (1 : ℝ) ≤ (1 + u ^ 2) ^ 2 := one_le_pow₀ (by nlinarith [sq_nonneg u])
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + u ^ 2) ^ 2),
      div_le_one (by positivity)]
    have h := Real.abs_log_mul_self_lt u h0 h1
    have e : u ^ 2 * log u = u * (log u * u) := by ring
    rw [e, abs_mul, abs_of_pos h0]
    nlinarith [abs_nonneg (log u * u)]
  · have hi := (integrableOn_Ioi_rpow_of_lt (a := -(3 / 2)) (by norm_num) zero_lt_one).const_mul 2
    refine Integrable.mono' hi hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hl : 0 ≤ log u := log_nonneg hu1.le
    unfold b2
    rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have hl2 : log u ≤ u ^ ((1 : ℝ) / 2) / (1 / 2) := log_le_rpow_div hu0.le (by norm_num)
    have e : u ^ ((1 : ℝ) / 2) = u ^ (-(3 / 2) : ℝ) * u ^ 2 := by
      rw [← rpow_natCast u 2, ← rpow_add hu0]
      norm_num
    have hr : 0 < u ^ (-(3 / 2) : ℝ) := rpow_pos_of_pos hu0 _
    have hl3 : log u ≤ 2 * (u ^ (-(3 / 2) : ℝ) * u ^ 2) := by
      rw [e] at hl2
      linarith
    have hq : u ^ 4 ≤ (1 + u ^ 2) ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
    calc u ^ 2 * log u ≤ u ^ 2 * (2 * (u ^ (-(3 / 2) : ℝ) * u ^ 2)) :=
          mul_le_mul_of_nonneg_left hl3 (by positivity)
      _ = 2 * u ^ (-(3 / 2) : ℝ) * u ^ 4 := by ring
      _ ≤ 2 * u ^ (-(3 / 2) : ℝ) * (1 + u ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hq (by positivity)

/-- The substitution `t = Au` in the main term. -/
theorem rvmF_mul_gA_scale {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    rvmF (A * u) * gA A (A * u) =
      2 / (π * A ^ 2) * ((log (A / (2 * π)) - 1) * b1 u + b2 u) := by
  have hpi : π ≠ 0 := pi_ne_zero
  have hl : log (A * u / (2 * π)) = log (A / (2 * π)) + log u := by
    rw [← log_mul (by positivity) hu.ne']
    congr 1
    ring
  unfold rvmF gA b1 b2
  rw [hl]
  set L := log (A / (2 * π))
  have h1 : 1 + u ^ 2 ≠ 0 := by positivity
  have h2 : A ^ 2 + (A * u) ^ 2 = A ^ 2 * (1 + u ^ 2) := by ring
  rw [h2]
  field_simp
  ring

theorem gA_scale {A u : ℝ} (hA : 0 < A) : gA A (A * u) = 4 * u / (A ^ 3 * (1 + u ^ 2) ^ 2) := by
  unfold gA
  have h2 : A ^ 2 + (A * u) ^ 2 = A ^ 2 * (1 + u ^ 2) := by ring
  rw [h2]
  have h1 : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp

/-- `(1 + √(Au)) g_A(Au) ≤ (8/A²) b₃(u)`, for `A ≥ 1`, `u > 0`. -/
theorem err_scale_le {A u : ℝ} (hA : 1 ≤ A) (hu : 0 < u) :
    (1 + √(A * u)) * gA A (A * u) ≤ 8 / A ^ 2 * b3 u := by
  have hA0 : 0 < A := by linarith
  rw [gA_scale hA0, Real.sqrt_mul hA0.le]
  unfold b3
  set s := √A with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg A
  have hsA : s ≤ A := by
    rw [hs]
    calc √A ≤ √(A * A) := Real.sqrt_le_sqrt (by nlinarith)
      _ = A := Real.sqrt_mul_self hA0.le
  have ht0 : 0 ≤ √u := Real.sqrt_nonneg u
  have hmain : 1 + s * √u ≤ 2 * A * (1 + √u) := by nlinarith [mul_le_mul_of_nonneg_right hsA ht0]
  have hq : 0 ≤ 4 * u / (A ^ 3 * (1 + u ^ 2) ^ 2) := by positivity
  calc (1 + s * √u) * (4 * u / (A ^ 3 * (1 + u ^ 2) ^ 2))
      ≤ (2 * A * (1 + √u)) * (4 * u / (A ^ 3 * (1 + u ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hmain hq
    _ = _ := by
        have h1 : 1 + u ^ 2 ≠ 0 := by positivity
        field_simp
        ring

theorem integrableOn_rvmF_mul_gA {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun t => rvmF t * gA A t) (Ioi 0) := by
  have h : IntegrableOn (fun u => 2 / (π * A ^ 2) * ((log (A / (2 * π)) - 1) * b1 u + b2 u)) (Ioi 0) :=
    ((integrable_b1.const_mul (log (A / (2 * π)) - 1)).add integrable_b2).const_mul
      (2 / (π * A ^ 2))
  have h2 : IntegrableOn (fun u => rvmF (A * u) * gA A (A * u)) (Ioi 0) :=
    h.congr_fun (fun u hu => (rvmF_mul_gA_scale hA hu).symm) measurableSet_Ioi
  have := (integrableOn_Ioi_comp_mul_left_iff (fun t => rvmF t * gA A t) 0 hA).mp h2
  simpa using this

theorem integrableOn_err {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun t => (1 + √t) * gA A t) (Ioi 0) := by
  have hA0 : 0 < A := by linarith
  have hm : Measurable (fun t => (1 + √t) * gA A t) := by
    unfold gA
    fun_prop
  have h2 : IntegrableOn (fun u => (1 + √(A * u)) * gA A (A * u)) (Ioi 0) := by
    refine Integrable.mono' (integrable_b3.const_mul (8 / A ^ 2))
      (hm.comp (measurable_const.mul measurable_id)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gA_nonneg (by positivity)))]
    exact err_scale_le hA hu0
  have := (integrableOn_Ioi_comp_mul_left_iff (fun t => (1 + √t) * gA A t) 0 hA0).mp h2
  simpa using this

/-- `∫_0^∞ F(t) g_A(t) dt = (2/(πA)) ((L−1) π/4 + c₂)`. -/
theorem integral_rvmF_mul_gA {A : ℝ} (hA : 0 < A) :
    ∫ t in Ioi (0 : ℝ), rvmF t * gA A t =
      (log (A / (2 * π)) - 1) / (2 * A) + 2 / (π * A) * ∫ u in Ioi (0 : ℝ), b2 u := by
  have h := integral_comp_mul_left_Ioi (fun t => rvmF t * gA A t) 0 hA
  rw [mul_zero] at h
  have h1 : ∫ u in Ioi (0 : ℝ), rvmF (A * u) * gA A (A * u) =
      2 / (π * A ^ 2) * ((log (A / (2 * π)) - 1) * (π / 4) + ∫ u in Ioi (0 : ℝ), b2 u) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => rvmF_mul_gA_scale hA hu),
      integral_const_mul, integral_add (integrable_b1.const_mul _) integrable_b2,
      integral_const_mul, integral_b1]
  rw [h1, smul_eq_mul] at h
  have hval : ∫ t in Ioi (0 : ℝ), rvmF t * gA A t =
      A * (2 / (π * A ^ 2) * ((log (A / (2 * π)) - 1) * (π / 4) + ∫ u in Ioi (0 : ℝ), b2 u)) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  rw [hval]
  have hpi : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- `∫_0^∞ (1+√t) g_A(t) dt ≤ 8 c₃/A`, for `A ≥ 1`. -/
theorem integral_err_le {A : ℝ} (hA : 1 ≤ A) :
    ∫ t in Ioi (0 : ℝ), (1 + √t) * gA A t ≤ 8 / A * ∫ u in Ioi (0 : ℝ), b3 u := by
  have hA0 : 0 < A := by linarith
  have h := integral_comp_mul_left_Ioi (fun t => (1 + √t) * gA A t) 0 hA0
  rw [mul_zero, smul_eq_mul] at h
  have hval : ∫ t in Ioi (0 : ℝ), (1 + √t) * gA A t =
      A * ∫ u in Ioi (0 : ℝ), (1 + √(A * u)) * gA A (A * u) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hA0.ne', one_mul]
  rw [hval]
  have hint2 : IntegrableOn (fun u => (1 + √(A * u)) * gA A (A * u)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun t => (1 + √t) * gA A t) 0 hA0).mpr
      (by simpa using integrableOn_err hA)
    exact this
  have hle : ∫ u in Ioi (0 : ℝ), (1 + √(A * u)) * gA A (A * u) ≤
      ∫ u in Ioi (0 : ℝ), 8 / A ^ 2 * b3 u :=
    setIntegral_mono_on hint2 (integrable_b3.const_mul _) measurableSet_Ioi
      fun u hu => err_scale_le hA hu
  rw [integral_const_mul] at hle
  calc A * ∫ u in Ioi (0 : ℝ), (1 + √(A * u)) * gA A (A * u)
      ≤ A * (8 / A ^ 2 * ∫ u in Ioi (0 : ℝ), b3 u) := mul_le_mul_of_nonneg_left hle hA0.le
    _ = _ := by
        field_simp

/-- `|σ_a² − log(A/2π)/(2A)| ≤ K/A`, for `A = a + ½ ≥ 1`. -/
theorem abs_sigmaSq_sub_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    ∃ K : ℝ, ∀ a : ℝ, 1 ≤ a + 1 / 2 →
      |sigmaSq a - log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2))| ≤ K / (a + 1 / 2) := by
  obtain ⟨lam, hmono, hpos, hrange, _⟩ := exists_ordinate_enum hN
  obtain ⟨C, hC0, hC⟩ := exists_zeroCount_sub_le hN hRH hLI hmono hpos hrange
  set c₂ := ∫ u in Ioi (0 : ℝ), b2 u with hc₂
  set c₃ := ∫ u in Ioi (0 : ℝ), b3 u with hc₃
  refine ⟨C * (8 * c₃) + 1 / 2 + 2 / π * |c₂|, fun a ha => ?_⟩
  set A := a + 1 / 2 with hAdef
  have hA0 : 0 < A := by linarith
  have hsig := sigmaSq_eq_integral hN hRH hLI hmono hpos hrange hA0
  have hmono2 := monotone_zeroCount hRH hLI hmono hpos hrange
  have hgm : Measurable (gA A) := by
    unfold gA
    fun_prop
  have hFi := integrableOn_rvmF_mul_gA hA0
  have hEi := integrableOn_err ha
  have hNi : IntegrableOn (fun t => (zeroCount t : ℝ) * gA A t) (Ioi 0) := by
    refine Integrable.mono' (hFi.norm.add (hEi.const_mul C))
      (hmono2.measurable.mul hgm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hg := gA_nonneg (A := A) ht0.le
    have hb := hC t ht0.le
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hg)]
    simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs]
    have : (zeroCount t : ℝ) ≤ |rvmF t| + C * (1 + √t) := by
      have h1 := (abs_le.mp hb).2
      have h2 := le_abs_self (rvmF t)
      linarith
    calc (zeroCount t : ℝ) * gA A t ≤ (|rvmF t| + C * (1 + √t)) * gA A t :=
          mul_le_mul_of_nonneg_right this hg
      _ = _ := by
          rw [abs_of_nonneg hg]
          ring
  have hdiff : ‖∫ t in Ioi (0 : ℝ), ((zeroCount t : ℝ) * gA A t - rvmF t * gA A t)‖ ≤
      ∫ t in Ioi (0 : ℝ), C * ((1 + √t) * gA A t) := by
    refine norm_integral_le_of_norm_le (hEi.const_mul C) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hg := gA_nonneg (A := A) ht0.le
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hg, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC t ht0.le) hg
  rw [integral_sub hNi hFi, ← hsig, integral_rvmF_mul_gA hA0, integral_const_mul,
    Real.norm_eq_abs] at hdiff
  have herr := integral_err_le ha
  rw [← hc₃] at herr
  have hE2 : C * ∫ t in Ioi (0 : ℝ), (1 + √t) * gA A t ≤ C * (8 / A * c₃) :=
    mul_le_mul_of_nonneg_left herr hC0
  set L := log (A / (2 * π)) with hL
  have hkey : sigmaSq a - L / (2 * A) =
      (sigmaSq a - ((L - 1) / (2 * A) + 2 / (π * A) * c₂)) +
        (-(1 / 2) / A + (2 / π * c₂) / A) := by
    have hpi : π ≠ 0 := pi_ne_zero
    field_simp
    ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  have h3 : |-(1 / 2) / A + (2 / π * c₂) / A| ≤ (1 / 2 + 2 / π * |c₂|) / A := by
    rw [← add_div, abs_div, abs_of_pos hA0]
    refine div_le_div_of_nonneg_right ?_ hA0.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / π)]
  have h4 : C * (8 / A * c₃) = C * (8 * c₃) / A := by
    field_simp
  calc _ ≤ C * (8 * c₃) / A + (1 / 2 + 2 / π * |c₂|) / A := by
        refine add_le_add ?_ h3
        rw [← h4]
        exact hdiff.trans hE2
    _ = _ := by
        field_simp
        ring

/-- **The variance.** Under RH and LI, `σ_a² ∼ log(A/2π)/(2A)` as `a → ∞`, with `A = a + ½`. -/
theorem sigmaSq_isEquivalent (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hLI : LI) :
    sigmaSq ~[atTop] fun a : ℝ => log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2)) := by
  obtain ⟨K, hK⟩ := abs_sigmaSq_sub_le hN hRH hLI
  have hAt : Tendsto (fun a : ℝ => a + 1 / 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hLt : Tendsto (fun a : ℝ => log ((a + 1 / 2) / (2 * π))) atTop atTop :=
    tendsto_log_atTop.comp (hAt.atTop_div_const (by positivity))
  have h1 : (fun a => sigmaSq a - log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2))) =O[atTop]
      fun a : ℝ => 1 / (a + 1 / 2) := by
    refine IsBigO.of_bound |K| ?_
    filter_upwards [hAt.eventually_ge_atTop 1] with a ha
    have hA0 : 0 < a + 1 / 2 := by linarith
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    refine (hK a ha).trans ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self K) hA0.le
  have h2 : (fun a : ℝ => 1 / (a + 1 / 2)) =o[atTop]
      fun a : ℝ => log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2)) := by
    refine IsLittleO.of_bound fun c hc => ?_
    filter_upwards [hAt.eventually_ge_atTop 1, hLt.eventually_ge_atTop (2 / c)] with a ha hL
    have hA0 : 0 < a + 1 / 2 := by linarith
    have hL0 : 0 < log ((a + 1 / 2) / (2 * π)) := lt_of_lt_of_le (by positivity) hL
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have h3 : 2 ≤ c * log ((a + 1 / 2) / (2 * π)) := by
      rw [div_le_iff₀ hc] at hL
      linarith
    rw [show c * (log ((a + 1 / 2) / (2 * π)) / (2 * (a + 1 / 2))) =
      (c * log ((a + 1 / 2) / (2 * π)) / 2) * (1 / (a + 1 / 2)) by field_simp]
    refine le_mul_of_one_le_left (by positivity) ?_
    linarith
  exact h1.trans_isLittleO h2

end CpsLean
