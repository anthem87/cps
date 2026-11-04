module

public import CpsLean.BiasLaw
public import CpsLean.BesselInt
public import CpsLean.SymmetricLaw
public import CpsLean.Classical.AnsThm19
public import CpsLean.Classical.BesselDecay
public import CpsLean.Classical.LI
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
set_option autoImplicit false

/-!
# The product `Π_{γ>0} J₀(2ξ/|½+a+iγ|)` and the characteristic function of `μ_a`

* `zeroDen a γ = |½ + a + iγ|`, `prodJ a ξ = Π_{γ>0} J₀(2ξ/|½+a+iγ|)`.
* `multipliable_prodJ`, `tendsto_prod_prodJ`: convergence of the product.
* `abs_prodJ_le_one`, `prodJ_neg`, `abs_prodJ_le_rpow`: size, parity, decay.
* `integral_exp_limiting`: under RH and LI, `∫ e^{iξt} dμ = e^{−iξ/(2a+1)·(−1)} P(ξ)`.
-/

open Real Filter Topology MeasureTheory Set Finset

@[expose] public section

namespace CpsLean

/-- `|½ + a + iγ|`. -/
noncomputable def zeroDen (a γ : ℝ) : ℝ := ‖((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)‖

/-- `Π_{γ>0} J₀(2ξ/|½+a+iγ|)`, over the positive ordinates of the zeros of `ζ`. -/
noncomputable def prodJ (a ξ : ℝ) : ℝ :=
  ∏' γ : zeroOrdinates, besselJ0 (2 * ξ / zeroDen a γ)

theorem zeroDen_sq (a γ : ℝ) : zeroDen a γ ^ 2 = (a + 1 / 2) ^ 2 + γ ^ 2 := by
  unfold zeroDen
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem zeroDen_pos (a : ℝ) {γ : ℝ} (hγ : 0 < γ) : 0 < zeroDen a γ := by
  have h0 : 0 ≤ zeroDen a γ := norm_nonneg _
  have h2 := zeroDen_sq a γ
  refine lt_of_le_of_ne h0 fun h => ?_
  rw [← h] at h2
  nlinarith [sq_nonneg (a + 1 / 2), pow_pos hγ 2]

section Enum

variable {lam : ℕ → ℝ}

/-- `Σ_n 1/|½+a+iλ_n|² < ∞`. -/
theorem summable_inv_zeroDen (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a : ℝ)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) :
    Summable (fun n => 1 / zeroDen a (lam n) ^ 2) := by
  obtain ⟨K, hK⟩ := sum_zeros_le hN a
  have hmem : ∀ n, lam n ∈ zeroOrdinates := fun n => hrange ▸ Set.mem_range_self n
  refine summable_of_sum_le (c := K) (fun n => by positivity) fun s => ?_
  classical
  have hinj : Set.InjOn (fun n => zeroOf (lam n)) (s : Set ℕ) := fun n _ k _ h =>
    hmono.injective (by simpa using congrArg Complex.im h)
  have := hK (s.image fun n => zeroOf (lam n)) (by
    intro ρ hρ
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact zeroOf_mem hRH (hmem n))
  rw [Finset.sum_image hinj] at this
  refine (Finset.sum_le_sum fun n _ => ?_).trans this
  have hm : (1 : ℝ) ≤ zeroMult (zeroOf (lam n)) := by
    exact_mod_cast zeroMult_pos (zeroOf_mem hRH (hmem n))
  have he : ‖zeroOf (lam n) + (a : ℂ)‖ = zeroDen a (lam n) := by
    unfold zeroDen zeroOf
    congr 1
    push_cast
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hm (by positivity)

/-- The summability behind the convergence of the product. -/
theorem summable_besselJ0_sub_one (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) :
    Summable (fun n => besselJ0 (2 * ξ / zeroDen a (lam n)) - 1) := by
  refine Summable.of_norm_bounded ((summable_inv_zeroDen hN hRH a hmono hrange).mul_left (2 * ξ ^ 2))
    fun n => ?_
  rw [Real.norm_eq_abs]
  refine (abs_besselJ0_sub_one_le _).trans (le_of_eq ?_)
  rw [div_pow]
  ring

/-- `ℕ ≃ ` positive ordinates. -/
noncomputable def ordEquiv (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) :
    ℕ ≃ zeroOrdinates :=
  Equiv.ofBijective (fun n => ⟨lam n, by rw [← hrange]; exact Set.mem_range_self n⟩)
    ⟨fun n k h => hmono.injective (congrArg Subtype.val h), fun γ => by
      have hγ : (γ : ℝ) ∈ Set.range lam := by rw [hrange]; exact γ.2
      obtain ⟨n, hn⟩ := hγ
      exact ⟨n, Subtype.ext hn⟩⟩

theorem multipliable_nat (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) :
    Multipliable (fun n => besselJ0 (2 * ξ / zeroDen a (lam n))) := by
  have := Real.multipliable_one_add_of_summable (summable_besselJ0_sub_one hN hRH a ξ hmono hrange)
  simpa using this

/-- The partial products converge to `prodJ`. -/
theorem tendsto_prod_prodJ (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) :
    Tendsto (fun N => ∏ n ∈ range N, besselJ0 (2 * ξ / zeroDen a (lam n))) atTop
      (𝓝 (prodJ a ξ)) := by
  have h := (multipliable_nat hN hRH a ξ hmono hrange).hasProd.tendsto_prod_nat
  have e : prodJ a ξ = ∏' n, besselJ0 (2 * ξ / zeroDen a (lam n)) := by
    unfold prodJ
    exact ((ordEquiv hmono hrange).tprod_eq
      (fun γ : zeroOrdinates => besselJ0 (2 * ξ / zeroDen a γ))).symm
  rw [e]
  exact h

theorem abs_prod_besselJ0_le_one (a ξ : ℝ) (s : Finset ℕ) :
    |∏ n ∈ s, besselJ0 (2 * ξ / zeroDen a (lam n))| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_besselJ0_le_one _

/-- Tail factors have size `≤ 1`: `|P(ξ)| ≤ |Π_{n<N}|`. -/
theorem abs_prodJ_le_prod (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ)
    (hmono : StrictMono lam) (hrange : Set.range lam = zeroOrdinates) (N : ℕ) :
    |prodJ a ξ| ≤ ∏ n ∈ range N, |besselJ0 (2 * ξ / zeroDen a (lam n))| := by
  refine le_of_tendsto (tendsto_prod_prodJ hN hRH a ξ hmono hrange).abs ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [Finset.abs_prod]
  have hsub : range N ⊆ range M := Finset.range_subset_range.mpr hM
  rw [← Finset.prod_sdiff hsub]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun _ _ => abs_besselJ0_le_one _

/-- Decay: `|P(ξ)| ≤ K (√|ξ|)^{−N}` for `|ξ|` large. -/
theorem abs_prodJ_le_pow (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (hB : BesselDecay)
    (a : ℝ) (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates) (N : ℕ) :
    ∃ K ξ₀ : ℝ, 0 ≤ K ∧ 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ |ξ| → |prodJ a ξ| ≤ K * ((√|ξ|)⁻¹) ^ N := by
  obtain ⟨C, hC⟩ := hB
  have hC0 : 0 ≤ C := by
    have := hC 1 (by simp)
    have h0 := abs_nonneg (besselJ0 1)
    simpa using h0.trans this
  have hd : ∀ n, 0 < zeroDen a (lam n) := fun n => zeroDen_pos a (hpos n)
  set ξ₀ : ℝ := 1 + ∑ n ∈ range N, zeroDen a (lam n) with hξ₀
  have hsum0 : 0 ≤ ∑ n ∈ range N, zeroDen a (lam n) :=
    Finset.sum_nonneg fun n _ => (hd n).le
  refine ⟨∏ n ∈ range N, (C * √(zeroDen a (lam n) / 2)), ξ₀,
    Finset.prod_nonneg fun n _ => by positivity, by positivity, fun ξ hξ => ?_⟩
  refine (abs_prodJ_le_prod hN hRH a ξ hmono hrange N).trans ?_
  have hξpos : 0 < |ξ| := by
    have : 0 < ξ₀ := by positivity
    linarith
  rw [show ((√|ξ|)⁻¹) ^ N = ∏ _n ∈ range N, (√|ξ|)⁻¹ by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun n hn => ?_
  have hdn := hd n
  have hle : zeroDen a (lam n) ≤ ξ₀ := by
    have := Finset.single_le_sum (f := fun n => zeroDen a (lam n)) (fun k _ => (hd k).le) hn
    linarith
  have hx : 1 ≤ |2 * ξ / zeroDen a (lam n)| := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos hdn, le_div_iff₀ hdn]
    linarith
  refine (hC _ hx).trans (le_of_eq ?_)
  rw [abs_div, abs_mul, abs_two, abs_of_pos hdn]
  have e : 2 * |ξ| / zeroDen a (lam n) = |ξ| / (zeroDen a (lam n) / 2) := by
    field_simp
  rw [e, Real.sqrt_div hξpos.le]
  have hs : 0 < √(zeroDen a (lam n) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < √|ξ| := Real.sqrt_pos.mpr hξpos
  field_simp

end Enum

theorem multipliable_prodJ (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ) :
    Multipliable (fun γ : zeroOrdinates => besselJ0 (2 * ξ / zeroDen a γ)) := by
  obtain ⟨lam, hmono, _, hrange, _⟩ := exists_ordinate_enum hN
  exact (ordEquiv hmono hrange).multipliable_iff.mp (multipliable_nat hN hRH a ξ hmono hrange)

theorem abs_prodJ_le_one (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a ξ : ℝ) :
    |prodJ a ξ| ≤ 1 := by
  obtain ⟨lam, hmono, _, hrange, _⟩ := exists_ordinate_enum hN
  simpa using abs_prodJ_le_prod hN hRH a ξ hmono hrange 0

theorem prodJ_neg (a ξ : ℝ) : prodJ a (-ξ) = prodJ a ξ := by
  unfold prodJ
  refine tprod_congr fun γ => ?_
  rw [mul_neg, neg_div, besselJ0_neg]

/-- Under LI, the frequencies are simple: `r_n = −2/(½+a+iλ_n)`, so `|r_n ξ| = 2|ξ|/|½+a+iλ_n|`. -/
theorem norm_coefA_mul {lam : ℕ → ℝ} (hRH : RiemannHypothesis) (hLI : LI) (a ξ : ℝ)
    (hpos : ∀ n, 0 < lam n) (hrange : Set.range lam = zeroOrdinates) (n : ℕ) :
    ‖coefA a lam n * (ξ : ℂ)‖ = 2 * |ξ| / zeroDen a (lam n) := by
  have hmem : lam n ∈ zeroOrdinates := hrange ▸ Set.mem_range_self n
  have hm : zeroMult (zeroOf (lam n)) = 1 :=
    hLI.1 _ (zeroOf_mem hRH hmem) (by simpa using hpos n)
  unfold coefA
  rw [hm, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
  simp only [Nat.cast_one, mul_one, norm_neg, Complex.norm_ofNat]
  unfold zeroDen
  ring

/-- **The characteristic function of `μ_a` under LI.** For every limiting distribution `μ` of
`E_a(e^y)`: `∫ e^{iξt} dμ = e^{−iξ/(2a+1)} P(ξ)`. -/
theorem integral_exp_limiting (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (h19 : AnsThm19) (hRH : RiemannHypothesis) (hLI : LI)
    {a : ℝ} (ha : -1 / 2 < a) {μ : ProbabilityMeasure ℝ}
    (hμ : HasLimitingDistribution (phiA a) μ) (ξ : ℝ) :
    ∫ t, Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) ∂(μ : Measure ℝ) =
      Complex.exp (Complex.I * ((-1 / (2 * a + 1) : ℝ) : ℂ) * (ξ : ℂ)) * (prodJ a ξ : ℂ) := by
  obtain ⟨lam, hmono, hpos, hrange, htop⟩ := exists_ordinate_enum hN
  have hexp := ansExpansion_phiA hE hN hK hRH ha hmono hpos hrange htop
  have hcond := ansCond_coefA hN hRH a hmono hpos hrange
  have hli : LinearIndependent ℚ lam :=
    hLI.2.2.comp (ordEquiv hmono hrange) (ordEquiv hmono hrange).injective
  have h := h19 _ _ _ _ _ hexp hcond hli μ hμ (-ξ)
  -- the partial products
  have hprod : ∀ N, ∏ n ∈ range N, ansJ0 ‖coefA a lam n * ((-ξ : ℝ) : ℂ)‖ =
      ((∏ n ∈ range N, besselJ0 (2 * ξ / zeroDen a (lam n)) : ℝ) : ℂ) := by
    intro N
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [ansJ0_eq, norm_coefA_mul hRH hLI a (-ξ) hpos hrange n, abs_neg]
    congr 1
    rcases abs_cases ξ with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, mul_neg, neg_div, besselJ0_neg]
  have hlim : Tendsto (fun N : ℕ => Complex.exp (-Complex.I * ((-1 / (2 * a + 1) : ℝ) : ℂ) * ((-ξ : ℝ) : ℂ)) *
      ((∏ n ∈ range N, besselJ0 (2 * ξ / zeroDen a (lam n)) : ℝ) : ℂ)) atTop
      (𝓝 (Complex.exp (-Complex.I * ((-1 / (2 * a + 1) : ℝ) : ℂ) * ((-ξ : ℝ) : ℂ)) * (prodJ a ξ : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_prod_prodJ hN hRH a ξ hmono hrange)).const_mul _
  have huniq := tendsto_nhds_unique (h.congr fun N => by rw [hprod N]) hlim
  have e1 : ∀ t : ℝ, Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ)) =
      Complex.exp (-Complex.I * ((-ξ : ℝ) : ℂ) * (t : ℂ)) := fun t => by
    congr 1
    push_cast
    ring
  simp_rw [e1]
  rw [huniq]
  congr 2
  push_cast
  ring

end CpsLean
