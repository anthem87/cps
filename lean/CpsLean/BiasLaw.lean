module

public import CpsLean.ZeroEnum
public import CpsLean.MeanLimit
public import CpsLean.Classical.AnsCor13a
public import CpsLean.Classical.AnsThm114
set_option autoImplicit false

/-!
# Theorem 3(i): the bias law

* `phiA a y = E_a(e^y)` for `y ≥ log 2` (the paper defines `E_a(x)` for `x ≥ 2`), `0` before.
* `coefA a lam n = r_n = −2 m_n/(½ + a + iλ_n)`, with `λ` an increasing enumeration of the positive
  ordinates and `m_n` the multiplicity.
* `ansExpansion_phiA`, `ansCond_coefA`: the hypotheses of Akbary–Ng–Shahabi.
* `mean_phiA`: `(1/Y) ∫_0^Y φ → −1/(2a+1)`.
* `theorem3_i`: **Theorem 3(i)**.
-/

open Real Filter Topology MeasureTheory Set Asymptotics

@[expose] public section

namespace CpsLean

/-- `φ(y) = E_a(e^y)`, for `y ≥ log 2`, and `0` before. -/
noncomputable def phiA (a y : ℝ) : ℝ := if log 2 ≤ y then errA a (exp y) else 0

/-- `ρ = ½ + iγ`. -/
noncomputable def zeroOf (γ : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ)

@[simp] theorem zeroOf_im (γ : ℝ) : (zeroOf γ).im = γ := by simp [zeroOf]

theorem eq_zeroOf (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) :
    ρ = zeroOf ρ.im := by
  apply Complex.ext
  · simp [zeroOf, re_eq_half hRH hρ]
  · simp

theorem zeroOf_mem (hRH : RiemannHypothesis) {γ : ℝ} (hγ : γ ∈ zeroOrdinates) :
    zeroOf γ ∈ nontrivialZeros := by
  obtain ⟨_, ρ, hρ, rfl⟩ := hγ
  rw [← eq_zeroOf hRH hρ]
  exact hρ

/-- `r_n = −2 m_n/(½ + a + iλ_n)`. -/
noncomputable def coefA (a : ℝ) (lam : ℕ → ℝ) (n : ℕ) : ℂ :=
  -2 * (zeroMult (zeroOf (lam n)) : ℂ) / (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (lam n : ℂ))

/-- `Σ_{λ_n≤T} r_n e^{iλ_n y} = −2 Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ)`. -/
theorem sum_coefA_eq (hRH : RiemannHypothesis) {lam : ℕ → ℝ} (hmono : StrictMono lam)
    (hrange : Set.range lam = zeroOrdinates) (a T y : ℝ) :
    ∑ᶠ n ∈ {n : ℕ | lam n ≤ T}, coefA a lam n * Complex.exp (Complex.I * (lam n : ℂ) * (y : ℂ)) =
      -2 * zeroSumPos T (raceTerm a y) := by
  have hmem : ∀ n, lam n ∈ zeroOrdinates := fun n => hrange ▸ Set.mem_range_self n
  have hbij := finsum_mem_eq_of_bijOn (s := {n : ℕ | lam n ≤ T})
    (t := {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T})
    (f := fun n => coefA a lam n * Complex.exp (Complex.I * (lam n : ℂ) * (y : ℂ)))
    (g := fun ρ => (-2 : ℂ) * ((zeroMult ρ : ℂ) * raceTerm a y ρ))
    (fun n => zeroOf (lam n)) ⟨?_, ?_, ?_⟩ ?_
  · rw [hbij, zeroSumPos_eq, Finset.mul_sum,
      finsum_mem_eq_finite_toFinset_sum _ (finite_band 0 T)]
    rfl
  · intro n hn
    refine ⟨zeroOf_mem hRH (hmem n), ?_, ?_⟩
    · simpa using (hmem n).1
    · simpa using hn
  · intro n _ k _ h
    have := congrArg Complex.im h
    simp only [zeroOf_im] at this
    exact hmono.injective this
  · rintro ρ ⟨h0, h1, h2⟩
    have hγ : ρ.im ∈ zeroOrdinates := ⟨h1, ρ, h0, rfl⟩
    rw [← hrange] at hγ
    obtain ⟨n, hn⟩ := hγ
    refine ⟨n, ?_, ?_⟩
    · change lam n ≤ T
      rw [hn]
      exact h2
    · change zeroOf (lam n) = ρ
      rw [hn]
      exact (eq_zeroOf hRH h0).symm
  · intro n _
    unfold coefA raceTerm
    simp only [zeroOf_im]
    ring

/-- `Y² e^{−Y/2} → 0`. -/
theorem tendsto_sq_mul_exp : Tendsto (fun Y : ℝ => Y ^ 2 * exp (-Y / 2)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
  have h2 := h.const_mul 4
  rw [mul_zero] at h2
  refine h2.congr fun Y => ?_
  simp only [Function.comp_apply, id]
  rw [neg_div]
  ring

theorem measurable_thetaPow (b : ℝ) : Measurable (thetaPow b) := (thetaPow_mono b).measurable

theorem continuousOn_li_exp {a : ℝ} (ha : -1 < a) :
    ContinuousOn (fun y : ℝ => li ((exp y) ^ (a + 1))) (Ici (log 2)) := by
  intro y hy
  have hy2 : (2 : ℝ) ≤ exp y := by
    rw [← log_le_iff_le_exp (by norm_num)]
    exact hy
  have hgt : 1 < (exp y) ^ (a + 1) := one_lt_rpow (by linarith) (by linarith)
  have hc : ContinuousAt (fun y : ℝ => (exp y) ^ (a + 1)) y :=
    continuous_exp.continuousAt.rpow_const (Or.inl (exp_pos y).ne')
  exact (ContinuousAt.comp (f := fun y : ℝ => (exp y) ^ (a + 1)) (g := li)
    (hasDerivAt_li hgt).continuousAt hc).continuousWithinAt

theorem continuous_weight (κ : ℝ) : Continuous (fun y : ℝ => log (exp y) / (exp y) ^ κ) := by
  simp only [log_exp]
  refine continuous_id.div (continuous_exp.rpow_const fun y => Or.inl (exp_pos y).ne') fun y => ?_
  exact (rpow_pos_of_pos (exp_pos y) κ).ne'

theorem measurable_phiA {a : ℝ} (ha : -1 < a) : Measurable (phiA a) := by
  classical
  set H : ℝ → ℝ := (Ici (log 2)).piecewise (fun y => li ((exp y) ^ (a + 1))) 0 with hH
  have hHm : Measurable H :=
    (continuousOn_li_exp ha).measurable_piecewise continuousOn_const measurableSet_Ici
  have hg : Measurable (fun y : ℝ => (thetaPow a (exp y) - H y) *
      (log (exp y) / (exp y) ^ (a + 1 / 2))) :=
    (((measurable_thetaPow a).comp measurable_exp).sub hHm).mul
      (continuous_weight _).measurable
  have heq : phiA a = fun y => if log 2 ≤ y then (thetaPow a (exp y) - H y) *
      (log (exp y) / (exp y) ^ (a + 1 / 2)) else 0 := by
    funext y
    unfold phiA
    split_ifs with h
    · have hHy : H y = li ((exp y) ^ (a + 1)) := by
        rw [hH]
        exact Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ici.mpr h)
      rw [hHy]
      rfl
    · rfl
  rw [heq]
  exact Measurable.ite measurableSet_Ici hg measurable_const

/-- `φ` is bounded on `[0, Y]`. -/
theorem phiA_bound {a : ℝ} (ha : -1 / 2 < a) (Y : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Set.Icc 0 Y, |phiA a y| ≤ B := by
  obtain ⟨Bh, hBh⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_li_exp (a := a) (by linarith)).mono
      (fun y (hy : y ∈ Set.Icc (log 2) Y) => (hy.1 : log 2 ≤ y)))
  have hθ : 0 ≤ thetaPow a (exp Y) := thetaPow_nonneg a (exp Y)
  refine ⟨(thetaPow a (exp Y) + |Bh|) * |Y|, by positivity, fun y hy => ?_⟩
  unfold phiA
  split_ifs with h
  · unfold errA
    rw [abs_mul, log_exp]
    have hy0 : 0 ≤ y := hy.1
    have hk0 : 0 ≤ a + 1 / 2 := by linarith
    have h1 : 1 ≤ (exp y) ^ (a + 1 / 2) := one_le_rpow (one_le_exp hy0) hk0
    have hw : |y / (exp y) ^ (a + 1 / 2)| ≤ |Y| := by
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_self hy0 h1).trans (hy.2.trans (le_abs_self Y))
    have hli := hBh y ⟨h, hy.2⟩
    rw [Real.norm_eq_abs] at hli
    have hθy : thetaPow a (exp y) ≤ thetaPow a (exp Y) :=
      thetaPow_mono a (exp_le_exp.mpr hy.2)
    have hθy0 := thetaPow_nonneg a (exp y)
    have hd : |thetaPow a (exp y) - li ((exp y) ^ (a + 1))| ≤ thetaPow a (exp Y) + |Bh| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hθy0]
      exact add_le_add hθy (hli.trans (le_abs_self Bh))
    exact mul_le_mul hd hw (abs_nonneg _) (by positivity)
  · rw [abs_zero]
    positivity

theorem integrableOn_phiA_sq {a : ℝ} (ha : -1 / 2 < a) (Y : ℝ) :
    IntegrableOn (fun y => phiA a y ^ 2) (Set.Icc 0 Y) := by
  obtain ⟨B, hB0, hB⟩ := phiA_bound ha Y
  refine Measure.integrableOn_of_bounded (M := B ^ 2) (by simp)
    ((measurable_phiA (a := a) (by linarith)).pow_const 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun y hy => ?_)
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (hB y hy) 2

theorem intervalIntegrable_phiA {a : ℝ} (ha : -1 / 2 < a) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (phiA a) volume u v := by
  obtain ⟨B, hB0, hB⟩ := phiA_bound ha v
  rw [intervalIntegrable_iff, uIoc_of_le huv]
  refine Measure.integrableOn_of_bounded (M := B) (by simp)
    (measurable_phiA (a := a) (by linarith)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun y hy => ?_)
  rw [Real.norm_eq_abs]
  exact hB y ⟨hu.trans hy.1.le, hy.2⟩

theorem log_two_le_log_three : log 2 ≤ log (3 : ℝ) := log_le_log (by norm_num) (by norm_num)

/-- `∫_u^v dy/y² = 1/u − 1/v`. -/
theorem integral_one_div_sq {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∫ y in u..v, 1 / y ^ 2 = 1 / u - 1 / v := by
  have hd : ∀ y ∈ uIcc u v, HasDerivAt (fun s : ℝ => -(1 / s)) (1 / y ^ 2) y := by
    intro y hy
    rw [uIcc_of_le huv] at hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have := ((hasDerivAt_inv hy0).neg)
    convert this using 1
    · funext s
      simp
    · simp
  have hc : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (uIcc u v) := by
    rw [uIcc_of_le huv]
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hy0)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- The form of Step 4 for `φ`. -/
theorem step4_phiA (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y y : ℝ, 2 ≤ Y → log 3 ≤ y → y ≤ Y →
      |phiA a y - (-1 / (2 * a + 1)) + 2 * (zeroSumPos (exp Y) (raceTerm a y)).re| ≤
        C * (1 / y + Y ^ 2 * exp (-Y / 2)) := by
  obtain ⟨C, hC, h⟩ := step4_assembling hE hN hK hRH ha
  refine ⟨C, hC, fun Y y hY hy hyY => ?_⟩
  have hphi : phiA a y = errA a (exp y) := if_pos (log_two_le_log_three.trans hy)
  have := h Y y hY hy hyY
  rw [hphi]
  convert this using 2
  ring

/-- **The expansion (1.6)–(1.7) of Akbary–Ng–Shahabi for `φ`.** -/
theorem ansExpansion_phiA (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a)
    {lam : ℕ → ℝ} (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates) (htop : Tendsto lam atTop atTop) :
    AnsExpansion (phiA a) (-1 / (2 * a + 1)) (log 3) lam (coefA a lam) := by
  obtain ⟨C, hC, hb⟩ := step4_phiA hE hN hK hRH ha
  have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  refine ⟨measurable_phiA (by linarith), integrableOn_phiA_sq ha, hl3.le, hmono, hpos, htop, ?_⟩
  set c := -1 / (2 * a + 1) with hc
  set A : ℝ → ℝ := fun Y => Y ^ 2 * exp (-Y / 2) with hA
  have hAt : Tendsto A atTop (𝓝 0) := tendsto_sq_mul_exp
  -- the bound
  have hbound : ∀ᶠ Y : ℝ in atTop,
      (1 / Y) * ∫ y in log 3..Y, (phiA a y - c -
        (∑ᶠ n ∈ {n : ℕ | lam n ≤ exp Y}, coefA a lam n *
          Complex.exp (Complex.I * (lam n : ℂ) * (y : ℂ))).re) ^ 2 ≤
        2 * C ^ 2 * (1 / log 3 * (1 / Y) + A Y ^ 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (log 3)] with Y hY hYl
    have hY0 : 0 < Y := by linarith
    have hA0 : 0 ≤ A Y := by
      simp only [hA]
      positivity
    set g : ℝ → ℝ := fun y => 2 * C ^ 2 * (1 / y ^ 2 + A Y ^ 2) with hg
    have hcont : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (uIcc (log 3) Y) := by
      rw [uIcc_of_le hYl]
      intro y hy
      have hy0 : y ≠ 0 := by linarith [hy.1]
      exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hy0)).continuousWithinAt
    have hgi : IntervalIntegrable g volume (log 3) Y :=
      ((hcont.intervalIntegrable).add intervalIntegrable_const).const_mul _
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hYl
      (f := fun y => (phiA a y - c - (∑ᶠ n ∈ {n : ℕ | lam n ≤ exp Y}, coefA a lam n *
          Complex.exp (Complex.I * (lam n : ℂ) * (y : ℂ))).re) ^ 2) (g := g)
      (ae_of_all _ fun y hy => by
        have hbd := hb Y y hY hy.1.le hy.2
        rw [sum_coefA_eq hRH hmono hrange]
        have hre : ((-2 : ℂ) * zeroSumPos (exp Y) (raceTerm a y)).re =
            -2 * (zeroSumPos (exp Y) (raceTerm a y)).re := by simp
        rw [hre, Real.norm_of_nonneg (by positivity)]
        have hy0 : 0 < y := by linarith [hy.1]
        set e := phiA a y - c - -2 * (zeroSumPos (exp Y) (raceTerm a y)).re with he
        have he' : |e| ≤ C * (1 / y + A Y) := by
          rw [he]
          convert hbd using 2
          ring
        have hsq : e ^ 2 ≤ (C * (1 / y + A Y)) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) he' 2
        have hu : (1 / y + A Y) ^ 2 ≤ 2 * (1 / y ^ 2 + A Y ^ 2) := by
          have : 1 / y ^ 2 = (1 / y) ^ 2 := by rw [div_pow, one_pow]
          rw [this]
          nlinarith [sq_nonneg (1 / y - A Y)]
        simp only [hg]
        calc e ^ 2 ≤ C ^ 2 * (1 / y + A Y) ^ 2 := by rw [← mul_pow]; exact hsq
          _ ≤ C ^ 2 * (2 * (1 / y ^ 2 + A Y ^ 2)) :=
              mul_le_mul_of_nonneg_left hu (by positivity)
          _ = _ := by ring) hgi
    have hgint : ∫ y in log 3..Y, g y =
        2 * C ^ 2 * ((1 / log 3 - 1 / Y) + A Y ^ 2 * (Y - log 3)) := by
      simp only [hg]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hcont.intervalIntegrable
        intervalIntegrable_const, integral_one_div_sq hl3 hYl, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hle := (le_abs_self _).trans hnorm
    rw [hgint] at hle
    calc _ ≤ (1 / Y) * (2 * C ^ 2 * ((1 / log 3 - 1 / Y) + A Y ^ 2 * (Y - log 3))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ _ := by
          have h1 : (1 / Y) * (A Y ^ 2 * (Y - log 3)) ≤ A Y ^ 2 := by
            have hq : (1 / Y) * (Y - log 3) ≤ 1 := by
              rw [one_div, inv_mul_le_iff₀ hY0]
              linarith
            calc (1 / Y) * (A Y ^ 2 * (Y - log 3)) = A Y ^ 2 * ((1 / Y) * (Y - log 3)) := by ring
              _ ≤ A Y ^ 2 * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
              _ = A Y ^ 2 := mul_one _
          have h2 : (1 / Y) * (1 / log 3 - 1 / Y) ≤ 1 / log 3 * (1 / Y) := by
            have : 0 ≤ (1 / Y) * (1 / Y) := by positivity
            nlinarith
          have hC2 : 0 ≤ 2 * C ^ 2 := by positivity
          have e : (1 / Y) * (2 * C ^ 2 * ((1 / log 3 - 1 / Y) + A Y ^ 2 * (Y - log 3))) =
              2 * C ^ 2 * ((1 / Y) * (1 / log 3 - 1 / Y) + (1 / Y) * (A Y ^ 2 * (Y - log 3))) := by
            ring
          rw [e]
          exact mul_le_mul_of_nonneg_left (add_le_add h2 h1) hC2
  have hlim : Tendsto (fun Y : ℝ => 2 * C ^ 2 * (1 / log 3 * (1 / Y) + A Y ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ => 1 / Y) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have := ((h1.const_mul (1 / log 3)).add (hAt.pow 2)).const_mul (2 * C ^ 2)
    simpa using this
  refine squeeze_zero' ?_ hbound hlim
  filter_upwards [eventually_ge_atTop (log 3), eventually_gt_atTop (0 : ℝ)] with Y hYl hY0
  have : 0 ≤ ∫ y in log 3..Y, (phiA a y - c -
      (∑ᶠ n ∈ {n : ℕ | lam n ≤ exp Y}, coefA a lam n *
        Complex.exp (Complex.I * (lam n : ℂ) * (y : ℂ))).re) ^ 2 :=
    intervalIntegral.integral_nonneg hYl fun y _ => by positivity
  exact mul_nonneg (by positivity) this

/-- A zero's multiplicity is bounded by the zeros in a unit band. -/
theorem zeroMult_le_band {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) (h1 : T < ρ.im) (h2 : ρ.im ≤ T + 1) :
    (zeroMult ρ : ℝ) ≤ zeroBand T (T + 1) := by
  unfold zeroBand
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_band T (T + 1))]
  have hmem : ρ ∈ (finite_band T (T + 1)).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨hρ, h1, h2⟩
  exact_mod_cast Finset.single_le_sum (f := fun ρ => zeroMult ρ) (fun _ _ => Nat.zero_le _) hmem

/-- **The condition (1.11) of Akbary–Ng–Shahabi**, with `β = ¾`. -/
theorem ansCond_coefA (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a : ℝ)
    {lam : ℕ → ℝ} (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates) : AnsCond13a lam (coefA a lam) := by
  have hmem : ∀ n, lam n ∈ zeroOrdinates := fun n => hrange ▸ Set.mem_range_self n
  obtain ⟨C₀, hC₀⟩ := (zeroBand_isBigO hN).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hC₀.and (eventually_ge_atTop (2 : ℝ)))
  constructor
  · -- the size of the coefficients
    set T₁ := max T₀ 2 with hT₁
    set M₁ : ℝ := ∑ ρ ∈ zerosLe (T₁ + 1), (zeroMult ρ : ℝ) with hM₁
    have hM₁0 : 0 ≤ M₁ := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hl0 := hpos 0
    refine ⟨3 / 4, by norm_num, 8 * |C₀| + 2 * M₁ * (lam 0) ^ (-(1 / 4 : ℝ)), fun n => ?_⟩
    have hln := hpos n
    set ρ := zeroOf (lam n) with hρdef
    have hρ : ρ ∈ nontrivialZeros := zeroOf_mem hRH (hmem n)
    have hρim : ρ.im = lam n := zeroOf_im _
    have hdenom : lam n ≤ ‖((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (lam n : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (lam n : ℂ))
      have h2 : (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (lam n : ℂ)).im = lam n := by simp
      rw [h2, abs_of_pos hln] at h
      exact h
    have hcoef : ‖coefA a lam n‖ ≤ 2 * (zeroMult ρ : ℝ) * (1 / lam n) := by
      unfold coefA
      rw [norm_div, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_natCast, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hln hdenom) (by positivity)
    have hsplit : (1 / lam n) = (lam n) ^ (-(1 / 4 : ℝ)) * (lam n) ^ (-(3 / 4 : ℝ)) := by
      rw [← rpow_add hln]
      norm_num
      rw [rpow_neg_one]
    have hp34 : 0 < (lam n) ^ (-(3 / 4 : ℝ)) := by positivity
    have hconst0 : 0 ≤ 2 * M₁ * (lam 0) ^ (-(1 / 4 : ℝ)) := by positivity
    rcases le_or_gt (T₁ + 1) (lam n) with hbig | hsmall
    · -- large ordinates
      have hTle : T₀ ≤ lam n - 1 := by
        have : T₀ ≤ T₁ := le_max_left _ _
        linarith
      obtain ⟨hb, hge⟩ := hT₀ _ hTle
      have hlogpos : 0 ≤ log (lam n - 1) := log_nonneg (by linarith)
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlogpos] at hb
      have hm : (zeroMult ρ : ℝ) ≤ zeroBand (lam n - 1) (lam n - 1 + 1) :=
        zeroMult_le_band hρ (by rw [hρim]; linarith) (by rw [hρim]; linarith)
      have hlog2 : log (lam n - 1) ≤ log (lam n) := log_le_log (by linarith) (by linarith)
      have hlog3 : log (lam n) ≤ (lam n) ^ ((1 : ℝ) / 4) / (1 / 4) :=
        log_le_rpow_div hln.le (by norm_num)
      have hm2 : (zeroMult ρ : ℝ) ≤ |C₀| * (4 * (lam n) ^ ((1 : ℝ) / 4)) := by
        have h1 : C₀ * log (lam n - 1) ≤ |C₀| * log (lam n - 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlogpos
        have h2 : log (lam n) ≤ 4 * (lam n) ^ ((1 : ℝ) / 4) := by
          have e : (lam n) ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * (lam n) ^ ((1 : ℝ) / 4) := by ring
          linarith
        calc (zeroMult ρ : ℝ) ≤ C₀ * log (lam n - 1) := hm.trans hb
          _ ≤ |C₀| * log (lam n - 1) := h1
          _ ≤ |C₀| * (4 * (lam n) ^ ((1 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_left (hlog2.trans h2) (abs_nonneg _)
      have hrp : (lam n) ^ ((1 : ℝ) / 4) * (1 / lam n) = (lam n) ^ (-(3 / 4 : ℝ)) := by
        have h1l : 1 / lam n = (lam n) ^ (-1 : ℝ) := by rw [rpow_neg_one, one_div]
        rw [h1l, ← rpow_add hln]
        norm_num
      calc ‖coefA a lam n‖ ≤ 2 * (zeroMult ρ : ℝ) * (1 / lam n) := hcoef
        _ ≤ 2 * (|C₀| * (4 * (lam n) ^ ((1 : ℝ) / 4))) * (1 / lam n) := by
            have : 0 ≤ 1 / lam n := by positivity
            nlinarith
        _ = 8 * |C₀| * ((lam n) ^ ((1 : ℝ) / 4) * (1 / lam n)) := by ring
        _ = 8 * |C₀| * (lam n) ^ (-(3 / 4 : ℝ)) := by rw [hrp]
        _ ≤ _ := by
            nlinarith
    · -- small ordinates
      have hm : (zeroMult ρ : ℝ) ≤ M₁ := by
        have hmemL : ρ ∈ zerosLe (T₁ + 1) := by
          refine mem_zerosLe.mpr ⟨hρ, ?_⟩
          rw [hρim, abs_of_pos hln]
          exact hsmall.le
        exact Finset.single_le_sum (f := fun ρ => (zeroMult ρ : ℝ))
          (fun _ _ => Nat.cast_nonneg _) hmemL
      have hl0n : lam 0 ≤ lam n := hmono.monotone (Nat.zero_le n)
      have hp14 : (lam n) ^ (-(1 / 4 : ℝ)) ≤ (lam 0) ^ (-(1 / 4 : ℝ)) :=
        (Real.rpow_le_rpow_iff_of_neg hln hl0 (by norm_num)).mpr hl0n
      calc ‖coefA a lam n‖ ≤ 2 * (zeroMult ρ : ℝ) * (1 / lam n) := hcoef
        _ ≤ 2 * M₁ * (1 / lam n) := by
            have : 0 ≤ 1 / lam n := by positivity
            nlinarith
        _ = 2 * M₁ * (lam n) ^ (-(1 / 4 : ℝ)) * (lam n) ^ (-(3 / 4 : ℝ)) := by rw [hsplit]; ring
        _ ≤ 2 * M₁ * (lam 0) ^ (-(1 / 4 : ℝ)) * (lam n) ^ (-(3 / 4 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hp34.le
            exact mul_le_mul_of_nonneg_left hp14 (by positivity)
        _ ≤ _ := by
            have : 0 ≤ 8 * |C₀| * (lam n) ^ (-(3 / 4 : ℝ)) := by positivity
            nlinarith
  · -- the number of frequencies in a unit interval
    refine ⟨|C₀|, ?_⟩
    filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 : ℝ)] with T hT hT2
    obtain ⟨hb, _⟩ := hT₀ T hT
    have hlog : 0 ≤ log T := log_nonneg (by linarith)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hlog] at hb
    have hcard : Nat.card {n : ℕ | T < lam n ∧ lam n ≤ T + 1} ≤ zeroBand T (T + 1) := by
      rw [Nat.card_coe_set_eq]
      have hle := Set.ncard_le_ncard_of_injOn (s := {n : ℕ | T < lam n ∧ lam n ≤ T + 1})
        (t := {ρ : ℂ | ρ ∈ nontrivialZeros ∧ T < ρ.im ∧ ρ.im ≤ T + 1}) (fun n => zeroOf (lam n))
        (fun n hn => ⟨zeroOf_mem hRH (hmem n), by simpa using hn.1, by simpa using hn.2⟩)
        (fun n _ k _ h => hmono.injective (by simpa using congrArg Complex.im h))
        (finite_band T (T + 1))
      refine hle.trans ?_
      rw [Set.ncard_eq_toFinset_card _ (finite_band T (T + 1))]
      unfold zeroBand
      rw [finsum_mem_eq_finite_toFinset_sum _ (finite_band T (T + 1)), Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      rw [Set.Finite.mem_toFinset] at hρ
      exact zeroMult_pos hρ.1
    have hcard' : (Nat.card {n : ℕ | T < lam n ∧ lam n ≤ T + 1} : ℝ) ≤ zeroBand T (T + 1) := by
      exact_mod_cast hcard
    exact hcard'.trans (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hlog))

theorem continuous_raceTerm (a : ℝ) (ρ : ℂ) : Continuous (fun y : ℝ => raceTerm a y ρ) := by
  unfold raceTerm
  exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).div_const _

theorem continuous_zeroSumPos_re (a T : ℝ) :
    Continuous (fun y : ℝ => (zeroSumPos T (raceTerm a y)).re) := by
  simp only [zeroSumPos_eq]
  exact Complex.continuous_re.comp
    (continuous_finsetSum _ fun ρ _ => continuous_const.mul (continuous_raceTerm a ρ))

/-- The norm of `∫_u^v e^{iγy}/(½ + a + iγ) dy` is at most `2/γ²`, for `γ > 0`. -/
theorem norm_integral_raceTerm_le (a : ℝ) {ρ : ℂ} (hγ : 0 < ρ.im) (u v : ℝ) :
    ‖∫ y in u..v, raceTerm a y ρ‖ ≤ 2 / ρ.im ^ 2 := by
  set γ := ρ.im with hγdef
  have hc : Complex.I * (γ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hγ.ne')
  have hnc : ‖Complex.I * (γ : ℂ)‖ = γ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hγ.le]
  have hexp : ∀ t : ℝ, ‖Complex.exp (Complex.I * (γ : ℂ) * (t : ℂ))‖ = 1 := by
    intro t
    have : Complex.I * (γ : ℂ) * (t : ℂ) = ((γ * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  set D : ℂ := ((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (γ : ℂ) with hD
  have hDn : γ ≤ ‖D‖ := by
    have h := Complex.abs_im_le_norm D
    have h2 : D.im = γ := by simp [hD]
    rw [h2, abs_of_pos hγ] at h
    exact h
  have hint : ∫ y in u..v, raceTerm a y ρ =
      ((Complex.exp (Complex.I * (γ : ℂ) * (v : ℂ)) - Complex.exp (Complex.I * (γ : ℂ) * (u : ℂ))) /
        (Complex.I * (γ : ℂ))) / D := by
    unfold raceTerm
    rw [intervalIntegral.integral_div, integral_exp_mul_complex hc]
  rw [hint, norm_div, norm_div, hnc]
  have hnum : ‖Complex.exp (Complex.I * (γ : ℂ) * (v : ℂ)) -
      Complex.exp (Complex.I * (γ : ℂ) * (u : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [hexp, hexp]
    norm_num
  have hDpos : 0 < ‖D‖ := hγ.trans_le hDn
  calc _ ≤ (2 / γ) / γ := by
        apply div_le_div₀ (by positivity) (div_le_div_of_nonneg_right hnum hγ.le) hγ hDn
    _ = 2 / γ ^ 2 := by field_simp

/-- `∫_u^v Re Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ) dy` is bounded uniformly in `T`, `u`, `v`. -/
theorem integral_zeroSumPos_le (hN : RiemannVonMangoldt) (hRH : RiemannHypothesis) (a : ℝ)
    {lam : ℕ → ℝ} (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T u v : ℝ, |∫ y in u..v, (zeroSumPos T (raceTerm a y)).re| ≤ K := by
  obtain ⟨K₀, hK₀⟩ := sum_zeros_le hN 0
  have hK₀0 : 0 ≤ K₀ := by simpa using hK₀ ∅ (by simp)
  have hl0 := hpos 0
  set L : ℝ := 1 + 1 / (4 * lam 0 ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨2 * L * K₀, by positivity, fun T u v => ?_⟩
  have hsub : (↑(zerosPos T) : Set ℂ) ⊆ nontrivialZeros :=
    fun ρ hρ => (mem_zerosPos.mp (Finset.mem_coe.mp hρ)).1
  have hsum := hK₀ (zerosPos T) hsub
  simp only [Complex.ofReal_zero, add_zero] at hsum
  have hri : ∀ ρ ∈ zerosPos T, IntervalIntegrable (fun y : ℝ => (zeroMult ρ : ℂ) * raceTerm a y ρ)
      volume u v := fun ρ _ => (continuous_const.mul (continuous_raceTerm a ρ)).intervalIntegrable _ _
  have hF : Continuous (fun y : ℝ => ∑ ρ ∈ zerosPos T, (zeroMult ρ : ℂ) * raceTerm a y ρ) :=
    continuous_finsetSum _ fun ρ _ => continuous_const.mul (continuous_raceTerm a ρ)
  have hre : ∫ y in u..v, (zeroSumPos T (raceTerm a y)).re =
      (∫ y in u..v, ∑ ρ ∈ zerosPos T, (zeroMult ρ : ℂ) * raceTerm a y ρ).re := by
    simp only [zeroSumPos_eq]
    exact Complex.reCLM.intervalIntegral_comp_comm (hF.intervalIntegrable _ _)
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [intervalIntegral.integral_finsetSum hri]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ρ ∈ zerosPos T, ‖∫ y in u..v, (zeroMult ρ : ℂ) * raceTerm a y ρ‖ ≤
      2 * L * ((zeroMult ρ : ℝ) / ‖ρ‖ ^ 2) := by
    intro ρ hρ
    obtain ⟨h0, h1, _⟩ := mem_zerosPos.mp hρ
    rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_natCast]
    have hb := norm_integral_raceTerm_le a h1 u v
    have hγ : ρ.im ∈ zeroOrdinates := ⟨h1, ρ, h0, rfl⟩
    rw [← hrange] at hγ
    obtain ⟨n, hn⟩ := hγ
    have hlam : lam 0 ≤ ρ.im := by
      rw [← hn]
      exact hmono.monotone (Nat.zero_le n)
    have hsq : lam 0 ^ 2 ≤ ρ.im ^ 2 := pow_le_pow_left₀ hl0.le hlam 2
    have hρn : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, re_eq_half hRH h0]
      ring
    have hle : ‖ρ‖ ^ 2 ≤ L * ρ.im ^ 2 := by
      rw [hρn, hL]
      have hk : 1 / 4 ≤ 1 / (4 * lam 0 ^ 2) * ρ.im ^ 2 := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hγ2 : 0 < ρ.im ^ 2 := by positivity
    have hρpos : 0 < ‖ρ‖ ^ 2 := by rw [hρn]; positivity
    have h2 : 2 / ρ.im ^ 2 ≤ 2 * L * (1 / ‖ρ‖ ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ hγ2 hρpos]
      nlinarith
    calc (zeroMult ρ : ℝ) * ‖∫ y in u..v, raceTerm a y ρ‖
        ≤ (zeroMult ρ : ℝ) * (2 * L * (1 / ‖ρ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hb.trans h2) (Nat.cast_nonneg _)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **The mean of `φ`**: `(1/Y) ∫_0^Y φ → −1/(2a+1)`. -/
theorem mean_phiA (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a)
    {lam : ℕ → ℝ} (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n)
    (hrange : Set.range lam = zeroOrdinates) :
    Tendsto (fun Y : ℝ => (1 / Y) * ∫ y in (0 : ℝ)..Y, phiA a y) atTop (𝓝 (-1 / (2 * a + 1))) := by
  obtain ⟨C, hC, hb⟩ := step4_phiA hE hN hK hRH ha
  obtain ⟨K, hK0, hKb⟩ := integral_zeroSumPos_le hN hRH a hmono hpos hrange
  set c := -1 / (2 * a + 1) with hc
  have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  set y₀ := log (3 : ℝ) with hy₀
  have hy₀1 : 1 < y₀ := one_lt_log_three
  set J := ∫ y in (0 : ℝ)..y₀, phiA a y with hJ
  set K₁ := |J| + |c| * y₀ + 2 * K with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set A : ℝ → ℝ := fun Y => Y ^ 2 * exp (-Y / 2) with hA
  rw [← tendsto_sub_nhds_zero_iff]
  have hbound : ∀ᶠ Y : ℝ in atTop, ‖(1 / Y) * (∫ y in (0 : ℝ)..Y, phiA a y) - c‖ ≤
      K₁ * (1 / Y) + C * (log Y / Y) + C * A Y := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : 0 < Y := by linarith
    have hyY : y₀ ≤ Y := by
      have : y₀ < 2 := by
        rw [hy₀, log_lt_iff_lt_exp (by norm_num)]
        have := Real.add_one_le_exp (2 : ℝ)
        have h2 : (3 : ℝ) < exp 2 := by
          have h1 := Real.exp_one_gt_d9
          have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
          rw [h2]
          nlinarith
        exact h2
      linarith
    have hA0 : 0 ≤ A Y := by
      simp only [hA]
      positivity
    set P : ℝ → ℝ := fun y => (zeroSumPos (exp Y) (raceTerm a y)).re with hP
    have hPc : Continuous P := continuous_zeroSumPos_re a (exp Y)
    have hφ1 := intervalIntegrable_phiA ha (le_refl (0 : ℝ)) hl3.le
    have hφ2 := intervalIntegrable_phiA ha hl3.le hyY
    set D : ℝ → ℝ := fun y => phiA a y - c + 2 * P y with hD
    have hDi : IntervalIntegrable D volume y₀ Y :=
      (hφ2.sub intervalIntegrable_const).add ((hPc.intervalIntegrable _ _).const_mul 2)
    have hsplit : ∫ y in (0 : ℝ)..Y, phiA a y = J + (c * (Y - y₀) - 2 * (∫ y in y₀..Y, P y) +
        ∫ y in y₀..Y, D y) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hφ1 hφ2]
      congr 1
      have h1 : ∫ y in y₀..Y, D y = (∫ y in y₀..Y, phiA a y) - c * (Y - y₀) +
          2 * ∫ y in y₀..Y, P y := by
        simp only [hD]
        rw [intervalIntegral.integral_add (hφ2.sub intervalIntegrable_const)
          ((hPc.intervalIntegrable _ _).const_mul 2),
          intervalIntegral.integral_sub hφ2 intervalIntegrable_const,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp only [smul_eq_mul]
        ring
      rw [h1]
      ring
    have hg : ContinuousOn (fun y : ℝ => C * (1 / y + A Y)) (uIcc y₀ Y) := by
      rw [uIcc_of_le hyY]
      intro y hy
      have hy0 : y ≠ 0 := by linarith [hy.1]
      exact (continuousAt_const.mul ((continuousAt_const.div continuousAt_id hy0).add
        continuousAt_const)).continuousWithinAt
    have hDn : ‖∫ y in y₀..Y, D y‖ ≤ ∫ y in y₀..Y, C * (1 / y + A Y) :=
      intervalIntegral.norm_integral_le_of_norm_le hyY
        (ae_of_all _ fun y hy => by
          have := hb Y y hY hy.1.le hy.2
          rw [Real.norm_eq_abs]
          simp only [hD, hP]
          convert this using 2)
        hg.intervalIntegrable
    have hgint : ∫ y in y₀..Y, C * (1 / y + A Y) = C * (log (Y / y₀) + A Y * (Y - y₀)) := by
      have hc1 : ContinuousOn (fun y : ℝ => 1 / y) (uIcc y₀ Y) := by
        rw [uIcc_of_le hyY]
        intro y hy
        have hy0 : y ≠ 0 := by linarith [hy.1]
        exact (continuousAt_const.div continuousAt_id hy0).continuousWithinAt
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hc1.intervalIntegrable
        intervalIntegrable_const, integral_one_div_of_pos hl3 hY0, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    have hlogq : log (Y / y₀) ≤ log Y := by
      rw [log_div hY0.ne' hl3.ne']
      have : 0 < log y₀ := log_pos hy₀1
      linarith
    have hDle : |∫ y in y₀..Y, D y| ≤ C * (log Y + A Y * Y) := by
      rw [← Real.norm_eq_abs]
      refine hDn.trans ?_
      rw [hgint]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have : A Y * (Y - y₀) ≤ A Y * Y := mul_le_mul_of_nonneg_left (by linarith) hA0
      linarith
    have hP2 : |∫ y in y₀..Y, P y| ≤ K := hKb _ _ _
    have heq : (1 / Y) * (∫ y in (0 : ℝ)..Y, phiA a y) - c =
        (1 / Y) * (J - c * y₀ - 2 * (∫ y in y₀..Y, P y) + ∫ y in y₀..Y, D y) := by
      rw [hsplit]
      field_simp
      ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < 1 / Y by positivity)]
    have htri : |J - c * y₀ - 2 * (∫ y in y₀..Y, P y) + ∫ y in y₀..Y, D y| ≤
        K₁ + C * (log Y + A Y * Y) := by
      have h1 := abs_add_le (J - c * y₀ - 2 * (∫ y in y₀..Y, P y)) (∫ y in y₀..Y, D y)
      have h2 := abs_sub (J - c * y₀) (2 * ∫ y in y₀..Y, P y)
      have h3 := abs_sub J (c * y₀)
      rw [abs_mul, abs_of_pos hl3] at h3
      rw [abs_mul, abs_two] at h2
      rw [hK₁]
      linarith
    calc 1 / Y * |J - c * y₀ - 2 * (∫ y in y₀..Y, P y) + ∫ y in y₀..Y, D y|
        ≤ 1 / Y * (K₁ + C * (log Y + A Y * Y)) := mul_le_mul_of_nonneg_left htri (by positivity)
      _ = K₁ * (1 / Y) + C * (log Y / Y) + C * A Y := by
          field_simp
          ring
  have hlim : Tendsto (fun Y : ℝ => K₁ * (1 / Y) + C * (log Y / Y) + C * A Y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ => 1 / Y) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h2 : Tendsto (fun Y : ℝ => log Y / Y) atTop (𝓝 0) :=
      isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have := ((h1.const_mul K₁).add (h2.const_mul C)).add ((tendsto_sq_mul_exp).const_mul C)
    simpa using this
  exact squeeze_zero_norm' hbound hlim

/-- **Theorem 3(i)** (Bias law). Assume RH. For every real `a > −½`, `E_a(e^y)` has a limiting
logarithmic distribution `μ_a`, and `∫ t dμ_a(t) = −1/(2a+1)`. -/
theorem theorem3_i (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hC : AnsCor13a) (hP : AnsThm114) (hRH : RiemannHypothesis)
    {a : ℝ} (ha : -1 / 2 < a) :
    ∃ μ : ProbabilityMeasure ℝ, HasLimitingDistribution (phiA a) μ ∧
      Integrable (fun t : ℝ => t) (μ : Measure ℝ) ∧
      ∫ t, t ∂(μ : Measure ℝ) = -1 / (2 * a + 1) := by
  obtain ⟨lam, hmono, hpos, hrange, htop⟩ := exists_ordinate_enum hN
  have hexp := ansExpansion_phiA hE hN hK hRH ha hmono hpos hrange htop
  have hcond := ansCond_coefA hN hRH a hmono hpos hrange
  obtain ⟨μ, hμ⟩ := hC _ _ _ _ _ hexp hcond
  have hsq := hP _ _ _ _ _ hexp hcond
  have hB : ∀ᶠ Y : ℝ in atTop, (1 / Y) * ∫ y in (0 : ℝ)..Y, phiA a y ^ 2 ≤
      ((-1 / (2 * a + 1)) ^ 2 + 1 / 2 * ∑' n, ‖coefA a lam n‖ ^ 2) + 1 :=
    (hsq.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨h1, h2⟩ := mean_of_limiting (measurable_phiA (by linarith)) (integrableOn_phiA_sq ha) hμ
    (mean_phiA hE hN hK hRH ha hmono hpos hrange) hB
  exact ⟨μ, hμ, h1, h2⟩

end CpsLean
