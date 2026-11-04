module

public import CpsLean.Classical.RiemannVonMangoldt
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false

/-!
# Counting the zeros of `ζ` from the Riemann–von Mangoldt formula

* `finite_zeros`: finitely many nontrivial zeros with `|γ| ≤ T`.
* `zeroMult_conj`: `m(ρ̄) = m(ρ)`.
* `zeroBand_isBigO` : `Σ_{T<γ≤T+1} m(ρ) ≪ log T`, from `RiemannVonMangoldt`.
* `sum_zeros_le`, `summable_zeros`: `Σ_ρ m(ρ)/|ρ + a|² < ∞` for every real `a`, from
  `RiemannVonMangoldt`.
-/

open Real Filter Asymptotics Topology Finset
open scoped ComplexConjugate

@[expose] public section

namespace CpsLean

/-- Finitely many nontrivial zeros with `|γ| ≤ T`. -/
theorem finite_zeros (T : ℝ) : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ |ρ.im| ≤ T}.Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨⟨h0, h1, h2⟩, hT⟩
  refine ⟨?_, h0⟩
  rw [mem_closedBall_zero_iff]
  have h3 := Complex.norm_le_abs_re_add_abs_im ρ
  have h4 := le_abs_self T
  rw [abs_of_pos h1] at h3
  linarith

/-- `Σ_{A<γ≤B} m(ρ)`. -/
noncomputable def zeroBand (A B : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B}, zeroMult ρ

theorem finite_band (A B : ℝ) : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B}.Finite := by
  refine (finite_zeros (max |A| |B|)).subset ?_
  rintro ρ ⟨h0, h1, h2⟩
  refine ⟨h0, ?_⟩
  rcases abs_cases ρ.im with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact le_max_of_le_right (h2.trans (le_abs_self B))
  · rw [h]
    refine le_max_of_le_left ?_
    have := neg_abs_le A
    have := neg_le_abs A
    linarith

/-- `N(B) = N(A) + Σ_{A<γ≤B} m(ρ)` for `0 ≤ A ≤ B`. -/
theorem zeroCount_add {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    zeroCount B = zeroCount A + zeroBand A B := by
  have hu : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ B} =
      {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ A} ∪
        {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨h0, h1, h2⟩
      rcases le_or_gt ρ.im A with h | h
      · exact Or.inl ⟨h0, h1, h⟩
      · exact Or.inr ⟨h0, h, h2⟩
    · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
      · exact ⟨h0, h1, h2.trans hAB⟩
      · exact ⟨h0, hA.trans_lt h1, h2⟩
  have hd : Disjoint {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ A}
      {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B} := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, _, h2⟩ ⟨_, h3, _⟩
    linarith
  unfold zeroCount zeroBand
  rw [hu, finsum_mem_union hd (finite_band 0 A) (finite_band A B)]

/-- `F(T) = (T/2π) log(T/2π) − T/2π`: the increment over a unit interval is `≪ log T`. -/
theorem rvmMain_increment_isBigO :
    (fun T : ℝ => ((T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - (T + 1) / (2 * π)) -
      (T / (2 * π) * log (T / (2 * π)) - T / (2 * π))) =O[atTop] (fun T : ℝ => log T) := by
  refine IsBigO.of_bound 3 ?_
  have hlog : Tendsto log atTop atTop := tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop (log (2 * π) + 2)] with T hT hT2
  have hT0 : 0 < T := by linarith
  have hpi : 0 < 2 * π := by positivity
  have hlogpi : 0 < log (2 * π) := by
    apply log_pos
    have := Real.pi_gt_three
    linarith
  have h1 : log ((T + 1) / (2 * π)) = log (T + 1) - log (2 * π) :=
    log_div (by positivity) hpi.ne'
  have h2 : log (T / (2 * π)) = log T - log (2 * π) := log_div hT0.ne' hpi.ne'
  have h3 : log (T + 1) - log T ≤ 1 / T := by
    have := log_le_sub_one_of_pos (show 0 < (T + 1) / T by positivity)
    rw [log_div (by positivity) hT0.ne'] at this
    have h : (T + 1) / T - 1 = 1 / T := by field_simp; ring
    linarith
  have h4 : 0 ≤ log (T + 1) - log T := by
    have := log_le_log hT0 (show T ≤ T + 1 by linarith)
    linarith
  have h5 : T * (log (T + 1) - log T) ≤ 1 := by
    calc T * (log (T + 1) - log T) ≤ T * (1 / T) := by gcongr
      _ = 1 := by field_simp
  have h6 : 0 ≤ T * (log (T + 1) - log T) := by positivity
  have h7 : log (T + 1) ≤ log T + 1 := by
    have : 1 / T ≤ 1 := by
      rw [div_le_one hT0]
      linarith
    linarith
  have hid : ((T + 1) / (2 * π) * log ((T + 1) / (2 * π)) - (T + 1) / (2 * π)) -
      (T / (2 * π) * log (T / (2 * π)) - T / (2 * π)) =
      (log (T + 1) - log (2 * π) + T * (log (T + 1) - log T) - 1) / (2 * π) := by
    rw [h1, h2]
    field_simp
    ring
  have hpi1 : 1 ≤ 2 * π := by
    have := Real.pi_gt_three
    linarith
  have hnum : |log (T + 1) - log (2 * π) + T * (log (T + 1) - log T) - 1| ≤ 3 * log T := by
    have hlT : 0 ≤ log T := by linarith
    have hlT1 : log T ≤ log (T + 1) := by linarith
    rw [abs_le]
    constructor <;> linarith
  rw [hid, Real.norm_eq_abs, abs_div, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ log T),
    abs_of_pos hpi]
  rw [div_le_iff₀ hpi]
  have hlT : 0 ≤ log T := by linarith
  nlinarith

/-- `log (T + 1) = O(log T)`. -/
theorem log_add_one_isBigO : (fun T : ℝ => log (T + 1)) =O[atTop] (fun T : ℝ => log T) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have h1 : log (T + 1) ≤ log (T ^ 2) := log_le_log (by linarith) (by nlinarith)
  rw [log_pow] at h1
  have h2 : 0 ≤ log T := log_nonneg (by linarith)
  have h3 : 0 ≤ log (T + 1) := log_nonneg (by linarith)
  rw [Real.norm_of_nonneg h3, Real.norm_of_nonneg h2]
  simpa using h1

/-- `Σ_{T<γ≤T+1} m(ρ) ≪ log T`, from the Riemann–von Mangoldt formula. -/
theorem zeroBand_isBigO (h : RiemannVonMangoldt) :
    (fun T : ℝ => (zeroBand T (T + 1) : ℝ)) =O[atTop] (fun T : ℝ => log T) := by
  have hshift : Tendsto (fun T : ℝ => T + 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have h1 := (h.comp_tendsto hshift).trans log_add_one_isBigO
  have h2 := (h1.sub h).add rvmMain_increment_isBigO
  refine h2.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have := zeroCount_add hT (show T ≤ T + 1 by linarith)
  simp only [Function.comp_apply, this]
  push_cast
  ring

/-! ### Conjugation -/

theorem analyticAt_conj_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 z) (𝓝 (conj z)) := Complex.continuous_conj.tendsto z
  filter_upwards [hc.eventually hf] with w hw
  exact differentiableAt_conj_conj_iff.mpr hw

/-- The order of `conj ∘ f ∘ conj` at `z` is the order of `f` at `z̄`, for `f` analytic at `z̄`. -/
theorem analyticOrderAt_conj_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f (conj z)) :
    analyticOrderAt (conj ∘ f ∘ conj) z = analyticOrderAt f (conj z) := by
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 z) (𝓝 (conj z)) := Complex.continuous_conj.tendsto z
  rcases eq_or_ne (analyticOrderAt f (conj z)) ⊤ with htop | htop
  · rw [htop, analyticOrderAt_eq_top]
    rw [analyticOrderAt_eq_top] at htop
    filter_upwards [hc.eventually htop] with w hw
    simp [hw]
  · have hn : analyticOrderAt f (conj z) = (analyticOrderNatAt f (conj z) : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt htop).symm
    rw [hn]
    rw [hf.analyticOrderAt_eq_natCast] at hn
    obtain ⟨g, hg, hg0, hfg⟩ := hn
    rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
    refine ⟨conj ∘ g ∘ conj, analyticAt_conj_conj hg, ?_, ?_⟩
    · simpa using hg0
    · filter_upwards [hc.eventually hfg] with w hw
      simp [hw, map_pow]

/-- Conjugate zeros have the same multiplicity. -/
theorem zeroMult_conj {ρ : ℂ} (hρ : ρ ≠ 1) : zeroMult (conj ρ) = zeroMult ρ := by
  have hfun : (conj ∘ riemannZeta ∘ conj : ℂ → ℂ) = riemannZeta := by
    funext w
    simp [riemannZeta_conj]
  have hρ' : conj ρ ≠ 1 := by
    intro h
    apply hρ
    simpa using congrArg conj h
  have han : AnalyticAt ℂ riemannZeta (conj ρ) := analyticOn_riemannZeta _ hρ'
  have := analyticOrderAt_conj_conj (z := ρ) han
  rw [hfun] at this
  unfold zeroMult analyticOrderNatAt
  rw [this]

theorem conj_mem_nontrivialZeros {ρ : ℂ} (h : ρ ∈ nontrivialZeros) : conj ρ ∈ nontrivialZeros := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, by simpa using h1, by simpa using h2⟩
  rw [riemannZeta_conj, h0, map_zero]

theorem ne_one_of_mem {ρ : ℂ} (h : ρ ∈ nontrivialZeros) : ρ ≠ 1 := by
  rintro rfl
  have := h.2.2
  simp at this

/-- `Σ_{A<|γ|≤B} m(ρ) = 2 Σ_{A<γ≤B} m(ρ)` for `0 ≤ A`. -/
noncomputable def zeroBandAbs (A B : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < |ρ.im| ∧ |ρ.im| ≤ B}, zeroMult ρ

theorem finite_bandAbs (A B : ℝ) :
    {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < |ρ.im| ∧ |ρ.im| ≤ B}.Finite :=
  (finite_zeros B).subset fun _ h => ⟨h.1, h.2.2⟩

theorem zeroBandAbs_eq {A B : ℝ} (hA : 0 ≤ A) : zeroBandAbs A B = 2 * zeroBand A B := by
  have hneg : ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < -ρ.im ∧ -ρ.im ≤ B}, zeroMult ρ =
      zeroBand A B := by
    unfold zeroBand
    refine finsum_mem_eq_of_bijOn (conj : ℂ → ℂ) ⟨?_, ?_, ?_⟩ ?_
    · rintro ρ ⟨h0, h1, h2⟩
      exact ⟨conj_mem_nontrivialZeros h0, by simpa using h1, by simpa using h2⟩
    · exact fun x _ y _ hxy => (RingEquiv.injective (starRingAut (R := ℂ))) hxy
    · rintro ρ ⟨h0, h1, h2⟩
      exact ⟨conj ρ, ⟨conj_mem_nontrivialZeros h0, by simpa using h1, by simpa using h2⟩, by simp⟩
    · rintro ρ ⟨h0, _, _⟩
      exact (zeroMult_conj (ne_one_of_mem h0)).symm
  have hu : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < |ρ.im| ∧ |ρ.im| ≤ B} =
      {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B} ∪
        {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < -ρ.im ∧ -ρ.im ≤ B} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨h0, h1, h2⟩
      rcases abs_cases ρ.im with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h] at h1 h2
        exact Or.inl ⟨h0, h1, h2⟩
      · rw [h] at h1 h2
        exact Or.inr ⟨h0, h1, h2⟩
    · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
      · have : |ρ.im| = ρ.im := abs_of_pos (hA.trans_lt h1)
        rw [this]
        exact ⟨h0, h1, h2⟩
      · have : |ρ.im| = -ρ.im := abs_of_neg (by linarith)
        rw [this]
        exact ⟨h0, h1, h2⟩
  have hd : Disjoint {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < ρ.im ∧ ρ.im ≤ B}
      {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < -ρ.im ∧ -ρ.im ≤ B} := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1, _⟩ ⟨_, h2, _⟩
    linarith
  have hfin : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ A < -ρ.im ∧ -ρ.im ≤ B}.Finite := by
    refine (finite_band (-B - 1) (-A)).subset ?_
    rintro ρ ⟨h0, h1, h2⟩
    exact ⟨h0, by linarith, by linarith⟩
  unfold zeroBandAbs
  rw [hu, finsum_mem_union hd (finite_band A B) hfin, hneg]
  change zeroBand A B + zeroBand A B = _
  ring

/-- `log k ≤ 2 √k`. -/
theorem log_le_two_sqrt {k : ℝ} (hk : 0 < k) : log k ≤ 2 * √k := by
  have h1 : log √k ≤ √k - 1 := log_le_sub_one_of_pos (sqrt_pos.mpr hk)
  have h2 : log √k = log k / 2 := log_sqrt hk.le
  rw [h2] at h1
  linarith

/-- The bound on the bands that the summability needs: `Σ_{k<|γ|≤k+1} m(ρ) ≤ C √k` for `k ≥ K`. -/
theorem exists_bandAbs_bound (h : RiemannVonMangoldt) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ 1 ≤ K ∧ ∀ k : ℕ, K ≤ k → (zeroBandAbs k (k + 1) : ℝ) ≤ C * √(k : ℝ) := by
  obtain ⟨C, hC⟩ := (zeroBand_isBigO h).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hC.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨4 * |C|, max 1 ⌈T₀⌉₊, by positivity, le_max_left _ _, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (le_max_left 1 ⌈T₀⌉₊).trans hk
  have hkT : T₀ ≤ k := (Nat.le_ceil T₀).trans (by exact_mod_cast (le_max_right 1 ⌈T₀⌉₊).trans hk)
  have hb := (hT₀ k hkT).1
  have hlog : 0 ≤ log (k : ℝ) := log_nonneg hk1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hlog] at hb
  rw [zeroBandAbs_eq (Nat.cast_nonneg k)]
  push_cast
  have h3 := log_le_two_sqrt (show (0 : ℝ) < k by linarith)
  have hCa : C ≤ |C| := le_abs_self C
  calc 2 * (zeroBand k (k + 1) : ℝ) ≤ 2 * (C * log k) := by gcongr
    _ ≤ 2 * (|C| * log k) := by gcongr
    _ ≤ 2 * (|C| * (2 * √(k : ℝ))) := by gcongr
    _ = 4 * |C| * √(k : ℝ) := by ring

/-- `Σ_{ρ∈s} m(ρ)/|ρ + a|²` is bounded uniformly in the finite set `s` of nontrivial zeros. -/
theorem sum_zeros_le (h : RiemannVonMangoldt) (a : ℝ) :
    ∃ K : ℝ, ∀ s : Finset ℂ, (↑s : Set ℂ) ⊆ nontrivialZeros →
      ∑ ρ ∈ s, (zeroMult ρ : ℝ) / ‖ρ + a‖ ^ 2 ≤ K := by
  obtain ⟨C, K₀, hC, hK₀, hband⟩ := exists_bandAbs_bound h
  set f : ℂ → ℝ := fun ρ => (zeroMult ρ : ℝ) / ‖ρ + a‖ ^ 2 with hf
  have hf0 : ∀ ρ, 0 ≤ f ρ := fun ρ => by positivity
  set Z₀ : Finset ℂ := (finite_zeros (K₀ : ℝ)).toFinset with hZ₀
  have hsumm : Summable (fun k : ℕ => C * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left C
  set G : ℕ → ℝ := fun k => C * (1 / (k : ℝ) ^ ((3 : ℝ) / 2)) with hG
  have hG0 : ∀ k, 0 ≤ G k := fun k => by positivity
  refine ⟨∑ ρ ∈ Z₀, f ρ + ∑' k, G k, fun s hs => ?_⟩
  -- the index of the band of a zero
  set idx : ℂ → ℕ := fun ρ => ⌈|ρ.im|⌉₊ - 1 with hidx
  have hsplit : ∑ ρ ∈ s, f ρ = ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ (K₀ : ℝ)), f ρ +
      ∑ ρ ∈ s.filter (fun ρ => ¬ |ρ.im| ≤ (K₀ : ℝ)), f ρ :=
    (Finset.sum_filter_add_sum_filter_not s _ f).symm
  rw [hsplit]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ _ _ => hf0 ρ
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    rw [hZ₀, Set.Finite.mem_toFinset]
    exact ⟨hs hρ.1, hρ.2⟩
  · set t := s.filter (fun ρ => ¬ |ρ.im| ≤ (K₀ : ℝ)) with ht
    have hfib := Finset.sum_fiberwise_of_maps_to (s := t) (t := t.image idx) (g := idx) (f := f)
      (fun ρ hρ => Finset.mem_image_of_mem _ hρ)
    rw [← hfib]
    refine (Finset.sum_le_sum (g := G) ?_).trans (hsumm.sum_le_tsum _ fun k _ => hG0 k)
    intro k hk
    obtain ⟨ρ₀, hρ₀, rfl⟩ := Finset.mem_image.mp hk
    have hρ₀' : (K₀ : ℝ) < |ρ₀.im| := by
      have := (Finset.mem_filter.mp hρ₀).2
      linarith [not_le.mp this]
    -- facts about the index
    have hbounds : ∀ ρ : ℂ, (K₀ : ℝ) < |ρ.im| →
        K₀ ≤ idx ρ ∧ (idx ρ : ℝ) < |ρ.im| ∧ |ρ.im| ≤ (idx ρ : ℝ) + 1 := by
      intro ρ hρ
      have hc1 : K₀ < ⌈|ρ.im|⌉₊ := Nat.lt_ceil.mpr hρ
      have hc2 : |ρ.im| ≤ ⌈|ρ.im|⌉₊ := Nat.le_ceil _
      have hc3 : (⌈|ρ.im|⌉₊ : ℝ) < |ρ.im| + 1 := Nat.ceil_lt_add_one (abs_nonneg _)
      have hcast : ((⌈|ρ.im|⌉₊ - 1 : ℕ) : ℝ) = (⌈|ρ.im|⌉₊ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      refine ⟨by simp only [hidx]; omega, ?_, ?_⟩
      · simp only [hidx]
        rw [hcast]
        linarith
      · simp only [hidx]
        rw [hcast]
        linarith
    obtain ⟨hk0, _, _⟩ := hbounds ρ₀ hρ₀'
    set k := idx ρ₀ with hkdef
    have hkpos : (0 : ℝ) < k := by
      have : 1 ≤ k := hK₀.trans hk0
      exact_mod_cast this
    have hfibsub : ∀ ρ ∈ t.filter (fun ρ => idx ρ = k),
        ρ ∈ (finite_bandAbs (k : ℝ) ((k : ℝ) + 1)).toFinset := by
      intro ρ hρ
      obtain ⟨hρt, hρk⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hρs, hρK⟩ := Finset.mem_filter.mp hρt
      have hρK' : (K₀ : ℝ) < |ρ.im| := not_le.mp hρK
      obtain ⟨_, h2, h3⟩ := hbounds ρ hρK'
      rw [hρk] at h2 h3
      rw [Set.Finite.mem_toFinset]
      exact ⟨hs hρs, h2, h3⟩
    have hterm : ∀ ρ ∈ t.filter (fun ρ => idx ρ = k), f ρ ≤ (zeroMult ρ : ℝ) * (1 / (k : ℝ) ^ 2) := by
      intro ρ hρ
      have hmem := hfibsub ρ hρ
      rw [Set.Finite.mem_toFinset] at hmem
      have hnorm : (k : ℝ) ≤ ‖ρ + a‖ := by
        have h1 : |(ρ + a).im| ≤ ‖ρ + a‖ := Complex.abs_im_le_norm _
        have h2 : (ρ + (a : ℂ)).im = ρ.im := by simp
        rw [h2] at h1
        linarith [hmem.2.1]
      simp only [hf]
      rw [div_eq_mul_one_div]
      gcongr
    have hsqrt : √(k : ℝ) * (1 / (k : ℝ) ^ 2) = 1 / (k : ℝ) ^ ((3 : ℝ) / 2) := by
      have h1 : √(k : ℝ) = (k : ℝ) ^ ((1 : ℝ) / 2) := sqrt_eq_rpow _
      have h2 : ((k : ℝ) ^ 2) = (k : ℝ) ^ (2 : ℝ) := by rw [rpow_two]
      rw [h1, h2, one_div (_ ^ (2 : ℝ)), one_div (_ ^ ((3 : ℝ) / 2)), ← rpow_neg hkpos.le,
        ← rpow_neg hkpos.le, ← rpow_add hkpos]
      norm_num
    calc ∑ ρ ∈ t with idx ρ = k, f ρ
        ≤ ∑ ρ ∈ t with idx ρ = k, (zeroMult ρ : ℝ) * (1 / (k : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ t with idx ρ = k, (zeroMult ρ : ℝ)) * (1 / (k : ℝ) ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ (zeroBandAbs (k : ℝ) ((k : ℝ) + 1) : ℝ) * (1 / (k : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          unfold zeroBandAbs
          rw [finsum_mem_eq_finite_toFinset_sum _ (finite_bandAbs (k : ℝ) ((k : ℝ) + 1))]
          push_cast
          exact Finset.sum_le_sum_of_subset_of_nonneg hfibsub fun _ _ _ => Nat.cast_nonneg _
      _ ≤ (C * √(k : ℝ)) * (1 / (k : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right (hband k hk0) (by positivity)
      _ = G k := by
          simp only [hG]
          rw [mul_assoc, hsqrt]

/-- `Σ_ρ m(ρ)/|ρ + a|² < ∞`, the sum over the nontrivial zeros, from the Riemann–von Mangoldt
formula. -/
theorem summable_zeros (h : RiemannVonMangoldt) (a : ℝ) :
    Summable (fun ρ : nontrivialZeros => (zeroMult (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) + a‖ ^ 2) := by
  obtain ⟨K, hK⟩ := sum_zeros_le h a
  refine summable_of_sum_le (c := K) (fun ρ => by positivity) fun s => ?_
  have := hK (s.map (Function.Embedding.subtype _)) (by
    intro ρ hρ
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hρ)
    exact x.2)
  rwa [Finset.sum_map] at this

end CpsLean
