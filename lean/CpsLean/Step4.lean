module

public import CpsLean.Layers
public import CpsLean.ZetaReal
public import CpsLean.BiasLayer
set_option autoImplicit false

/-!
# Theorem 3, Step 4: assembling

* `errA a x = E_a(x) = (θ_a(x) − li(x^{a+1})) log x / x^{a+½}`.
* `zeroSumPos T f = Σ_{0<γ≤T} f(ρ)`, with multiplicity.
* `zeroSumLe_eq_two_re`: under RH, the sum over `|γ| ≤ T` is `2 Re` of the sum over `0 < γ ≤ T`.
* `step2_uniform`: the boxed formula of Step 2, with a constant valid for all `x ≥ 3`.
* `step4_assembling`: **Theorem 3, Step 4**.
-/

open Finset Real Filter Topology Asymptotics
open scoped ComplexConjugate

@[expose] public section

namespace CpsLean

/-- `E_a(x) = (θ_a(x) − li(x^{a+1})) log x / x^{a+½}`. -/
noncomputable def errA (a x : ℝ) : ℝ :=
  (thetaPow a x - li (x ^ (a + 1))) * (log x / x ^ (a + 1 / 2))

/-- `Σ_{0<γ≤T} f(ρ)` over the nontrivial zeros `ρ = β + iγ`, with multiplicity. -/
noncomputable def zeroSumPos (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T}, (zeroMult ρ : ℂ) * f ρ

/-- The finite set of the nontrivial zeros with `0 < γ ≤ T`. -/
noncomputable def zerosPos (T : ℝ) : Finset ℂ := (finite_band 0 T).toFinset

theorem mem_zerosPos {T : ℝ} {ρ : ℂ} : ρ ∈ zerosPos T ↔ ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  rw [zerosPos, Set.Finite.mem_toFinset]
  rfl

theorem zeroSumPos_eq (T : ℝ) (f : ℂ → ℂ) :
    zeroSumPos T f = ∑ ρ ∈ zerosPos T, (zeroMult ρ : ℂ) * f ρ := by
  unfold zeroSumPos zerosPos
  exact finsum_mem_eq_finite_toFinset_sum _ _

/-- Under RH, no nontrivial zero has ordinate `0`. -/
theorem im_ne_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) : ρ.im ≠ 0 := by
  intro h
  have hre := re_eq_half hRH hρ
  have hρ2 : ρ = ((1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hre, h]
  have h0 := hρ.1
  rw [hρ2] at h0
  exact riemannZeta_ne_zero_of_real (σ := 1 / 2) (by norm_num) (by norm_num) h0

/-- The term of the race: `g(ρ) = e^{iγy}/(½ + a + iγ)`. -/
noncomputable def raceTerm (a y : ℝ) (ρ : ℂ) : ℂ :=
  Complex.exp (Complex.I * (ρ.im : ℂ) * (y : ℂ)) / (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ))

theorem raceTerm_conj (a y : ℝ) (ρ : ℂ) : raceTerm a y (conj ρ) = conj (raceTerm a y ρ) := by
  have hN : conj (Complex.I * (ρ.im : ℂ) * (y : ℂ)) = Complex.I * ((conj ρ).im : ℂ) * (y : ℂ) := by
    simp [Complex.conj_ofReal]
  have hD : conj (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ)) =
      ((a + 1 / 2 : ℝ) : ℂ) + Complex.I * ((conj ρ).im : ℂ) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
    simp
  unfold raceTerm
  rw [map_div₀, ← Complex.exp_conj, hN, hD]

/-- **Pairing the conjugate zeros**: under RH, for `x = e^y`,
`Σ_{|γ|≤T} x^{iγ}/(ρ + a) = 2 Re Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ)`. -/
theorem zeroSumLe_eq_two_re (hRH : RiemannHypothesis) (a y T : ℝ) :
    zeroSumLe T (fun ρ => ((exp y : ℝ) : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ))) =
      ((2 * (zeroSumPos T (raceTerm a y)).re : ℝ) : ℂ) := by
  have hterm : ∀ ρ ∈ zerosLe T, ((exp y : ℝ) : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ)) =
      raceTerm a y ρ := by
    intro ρ hρ
    have hρ' := (mem_zerosLe.mp hρ).1
    have hne : ((exp y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (exp_pos y).ne'
    have hs : ρ + (a : ℂ) = ((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ) := by
      apply Complex.ext
      · simp [re_eq_half hRH hρ']
        ring
      · simp
    unfold raceTerm
    rw [hs, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (exp_pos y).le, log_exp]
    congr 2
    ring
  have hsplit := Finset.sum_filter_add_sum_filter_not (zerosLe T) (fun ρ => 0 < ρ.im)
    (fun ρ => (zeroMult ρ : ℂ) * raceTerm a y ρ)
  have hpos : (zerosLe T).filter (fun ρ => 0 < ρ.im) = zerosPos T := by
    ext ρ
    simp only [Finset.mem_filter, mem_zerosLe, mem_zerosPos]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h2, (le_abs_self _).trans h1⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by rwa [abs_of_pos h1]⟩, h1⟩
  have hneg : ∑ ρ ∈ (zerosLe T).filter (fun ρ => ¬ 0 < ρ.im), (zeroMult ρ : ℂ) * raceTerm a y ρ =
      ∑ ρ ∈ zerosPos T, (zeroMult ρ : ℂ) * conj (raceTerm a y ρ) := by
    refine Finset.sum_bij' (fun ρ _ => conj ρ) (fun ρ _ => conj ρ) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      obtain ⟨hρ1, hρ2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨h0, h1⟩ := mem_zerosLe.mp hρ1
      have hne := im_ne_zero hRH h0
      have hlt : ρ.im < 0 := lt_of_le_of_ne (not_lt.mp hρ2) hne
      refine mem_zerosPos.mpr ⟨conj_mem_nontrivialZeros h0, by simpa using hlt, ?_⟩
      rw [abs_of_neg hlt] at h1
      simpa using h1
    · intro ρ hρ
      obtain ⟨h0, h1, h2⟩ := mem_zerosPos.mp hρ
      refine Finset.mem_filter.mpr ⟨mem_zerosLe.mpr ⟨conj_mem_nontrivialZeros h0, ?_⟩, ?_⟩
      · simp only [Complex.conj_im, abs_neg]
        rwa [abs_of_pos h1]
      · simp only [Complex.conj_im, not_lt]
        linarith
    · intro ρ _
      simp
    · intro ρ _
      simp
    · intro ρ hρ
      obtain ⟨hρ1, _⟩ := Finset.mem_filter.mp hρ
      obtain ⟨h0, _⟩ := mem_zerosLe.mp hρ1
      rw [← raceTerm_conj, zeroMult_conj (ne_one_of_mem h0)]
      simp
  rw [zeroSumLe_eq, Finset.sum_congr rfl (fun ρ hρ => by rw [hterm ρ hρ]), ← hsplit, hpos, hneg,
    zeroSumPos_eq, ← Finset.sum_add_distrib, Complex.re_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hm : ((zeroMult ρ : ℂ) * raceTerm a y ρ).re = (zeroMult ρ : ℝ) * (raceTerm a y ρ).re := by
    simp
  have hc : raceTerm a y ρ + conj (raceTerm a y ρ) = ((2 * (raceTerm a y ρ).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  rw [hm, ← mul_add, hc]
  push_cast
  ring

theorem thetaPow_mono (b : ℝ) : Monotone (thetaPow b) := by
  intro y z hyz
  unfold thetaPow
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨?_, hp2⟩
  obtain ⟨h0, h1⟩ := Finset.mem_Icc.mp hp1
  exact Finset.mem_Icc.mpr ⟨h0, h1.trans (Nat.floor_le_floor hyz)⟩

/-- **The boxed formula of Step 2, for all `x ≥ 3`**. -/
theorem step2_uniform (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x →
      |(1 / 2) * thetaPow (2 * a) √x - x ^ (a + 1 / 2) / ((2 * a + 1) * log x)| ≤
        C * (x ^ (a + 1 / 2) / log x ^ 2) := by
  have h2a : 0 < 2 * a + 1 := by linarith
  set κ := a + 1 / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨c, hc⟩ := (step2_bias_layer hK hRH ha).bound
  obtain ⟨x₀', hx₀'⟩ := eventually_atTop.mp hc
  set x₀ := max x₀' 3 with hx₀
  have hx₀3 : 3 ≤ x₀ := le_max_right _ _
  have hlx₀ : 0 < log x₀ := log_pos (by linarith)
  set M := (1 / 2) * thetaPow (2 * a) √x₀ + x₀ ^ κ / ((2 * a + 1) * log 3) with hM
  have hM0 : 0 ≤ M := by
    have := thetaPow_nonneg (2 * a) √x₀
    have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
    positivity
  refine ⟨|c| / (2 * a + 1) + M * log x₀ ^ 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl1 : 1 < log x := one_lt_log_three.trans_le (log_le_log (by norm_num) hx)
  have hl : 0 < log x := by linarith
  have hxk : 0 < x ^ κ := by positivity
  have hE : 0 < x ^ κ / log x ^ 2 := by positivity
  rcases le_or_gt x₀ x with hbig | hsmall
  · have h := hx₀' x ((le_max_left _ _).trans hbig)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at h
    have heq : x ^ κ / ((2 * a + 1) * log x) / log x = 1 / (2 * a + 1) * (x ^ κ / log x ^ 2) := by
      field_simp
    rw [heq] at h
    have h1 : c * (1 / (2 * a + 1) * (x ^ κ / log x ^ 2)) ≤
        |c| / (2 * a + 1) * (x ^ κ / log x ^ 2) := by
      have : c * (1 / (2 * a + 1) * (x ^ κ / log x ^ 2)) =
          c / (2 * a + 1) * (x ^ κ / log x ^ 2) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ hE.le
      exact div_le_div_of_nonneg_right (le_abs_self c) h2a.le
    have h2 : 0 ≤ M * log x₀ ^ 2 * (x ^ κ / log x ^ 2) := by positivity
    have e := add_mul (|c| / (2 * a + 1)) (M * log x₀ ^ 2) (x ^ κ / log x ^ 2)
    linarith
  · -- on the compact `[3, x₀]`
    have hs : √x ≤ √x₀ := sqrt_le_sqrt hsmall.le
    have ht := thetaPow_mono (2 * a) hs
    have ht0 := thetaPow_nonneg (2 * a) √x
    have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
    have hl3x : log 3 ≤ log x := log_le_log (by norm_num) hx
    have hpk : x ^ κ ≤ x₀ ^ κ := rpow_le_rpow hx0.le hsmall.le hκ0.le
    have hb2 : x ^ κ / ((2 * a + 1) * log x) ≤ x₀ ^ κ / ((2 * a + 1) * log 3) := by
      apply div_le_div₀ (by positivity) hpk (by positivity)
      exact mul_le_mul_of_nonneg_left hl3x h2a.le
    have hb20 : 0 ≤ x ^ κ / ((2 * a + 1) * log x) := by positivity
    have habs : |(1 / 2) * thetaPow (2 * a) √x - x ^ κ / ((2 * a + 1) * log x)| ≤ M := by
      rw [abs_le]
      constructor <;> rw [hM] <;> nlinarith
    refine habs.trans ?_
    have hone : 1 ≤ log x₀ ^ 2 * (x ^ κ / log x ^ 2) := by
      have h1 : log x ≤ log x₀ := log_le_log hx0 hsmall.le
      have h2 : log x ^ 2 ≤ log x₀ ^ 2 := pow_le_pow_left₀ hl.le h1 2
      have h3 : (1 : ℝ) ≤ x ^ κ := one_le_rpow (by linarith) hκ0.le
      rw [mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
      have hp : 0 ≤ log x₀ ^ 2 := by positivity
      nlinarith
    have h3 : M ≤ M * log x₀ ^ 2 * (x ^ κ / log x ^ 2) := by
      calc M = M * 1 := (mul_one M).symm
        _ ≤ M * (log x₀ ^ 2 * (x ^ κ / log x ^ 2)) := mul_le_mul_of_nonneg_left hone hM0
        _ = _ := by ring
    have h4 : 0 ≤ |c| / (2 * a + 1) * (x ^ κ / log x ^ 2) := by positivity
    have e := add_mul (|c| / (2 * a + 1)) (M * log x₀ ^ 2) (x ^ κ / log x ^ 2)
    linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem 3, Step 4** (assembling). Assume RH. For `a > −½`, `Y ≥ 2`, `T = e^Y`,
`log 3 ≤ y ≤ Y`,
`E_a(e^y) = −1/(2a+1) − 2 Re Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ) + ε_a(y, T)` with
`|ε_a(y, T)| ≪_a 1/y + Y² e^{−Y/2}`. -/
theorem step4_assembling (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hK : LeanBase.VonKochPsi) (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y y : ℝ, 2 ≤ Y → log 3 ≤ y → y ≤ Y →
      |errA a (exp y) - (-1 / (2 * a + 1) - 2 * (zeroSumPos (exp Y) (raceTerm a y)).re)| ≤
        C * (1 / y + Y ^ 2 * exp (-Y / 2)) := by
  obtain ⟨CA, hCA⟩ := lemmaA hE hN hRH ha
  obtain ⟨C₂, hC₂, hb2⟩ := step2_uniform hK hRH ha
  obtain ⟨C₃, hC₃, hb3⟩ := layersR_le ha
  set κ := a + 1 / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨D, hD, hDb⟩ := log_pow_le_rpow 2 hκ0
  have h2a : 0 < 2 * a + 1 := by linarith
  refine ⟨(|CA| + C₂ + C₃) + |CA| * D + |CA|, by positivity, fun Y y hY hy hyY => ?_⟩
  have hl3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
  have hy0 : 0 < y := by linarith
  set x := exp y with hx
  have hx0 : 0 < x := exp_pos y
  have hlogx : log x = y := log_exp y
  have hx3 : 3 ≤ x := by
    rw [hx, ← log_le_iff_le_exp (by norm_num)]
    exact hy
  have hxY : x ≤ exp Y := exp_le_exp.mpr hyY
  set S : ℝ := 2 * (zeroSumPos (exp Y) (raceTerm a y)).re with hS
  have hA := hCA Y x hY hx3 hxY
  rw [hx, zeroSumLe_eq_two_re hRH a y (exp Y), ← hx, ← hS, hlogx] at hA
  -- `e_A`
  set eA : ℝ := piA a x - (li (x ^ (a + 1)) - x ^ κ / y * S) with heA
  have hAreal : |eA| ≤ CA * (x ^ κ / y ^ 2 + Y ^ 2 * exp (-Y / 2) * (x ^ κ / y) + 1) := by
    have hcast : ((piA a x : ℝ) : ℂ) - (((li (x ^ (a + 1)) : ℝ) : ℂ) -
        ((x ^ κ / y : ℝ) : ℂ) * ((S : ℝ) : ℂ)) = ((eA : ℝ) : ℂ) := by
      rw [heA]
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hA
    exact hA
  set e₂ : ℝ := (1 / 2) * thetaPow (2 * a) √x - x ^ κ / ((2 * a + 1) * y) with he₂
  have h2' : |e₂| ≤ C₂ * (x ^ κ / y ^ 2) := by
    have := hb2 x hx3
    rwa [hlogx] at this
  set R := layersR a x with hR
  have h3' : R ≤ C₃ * (x ^ κ / y ^ 2) := by
    have := hb3 x hx3
    rwa [hlogx] at this
  have hR0 : 0 ≤ R := layersR_nonneg a x
  have hlayers := piA_eq_layers a hx0.le
  have hxk : 0 < x ^ κ := by positivity
  -- the identity
  have hid : errA a x - (-1 / (2 * a + 1) - S) = (eA - e₂ - R) * (y / x ^ κ) := by
    unfold errA
    rw [hlogx, ← hκ]
    have ht : thetaPow a x = piA a x - (1 / 2) * thetaPow (2 * a) √x - R := by
      rw [hR]
      linarith
    rw [ht, heA, he₂]
    generalize x ^ κ = X at hxk ⊢
    generalize piA a x = P
    generalize thetaPow (2 * a) √x = Q
    generalize li (x ^ (a + 1)) = L
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos (show 0 < y / x ^ κ by positivity)]
  set Ex := x ^ κ / y ^ 2 with hEx
  set Ey := Y ^ 2 * exp (-Y / 2) with hEy
  have hEy0 : 0 ≤ Ey := by positivity
  have hsum : |eA - e₂ - R| ≤ (|CA| + C₂ + C₃) * Ex + |CA| * Ey * (x ^ κ / y) + |CA| := by
    have ht1 : |eA - e₂ - R| ≤ |eA| + |e₂| + R := by
      have h1 := abs_sub (eA - e₂) R
      have h2 := abs_sub eA e₂
      rw [abs_of_nonneg hR0] at h1
      linarith
    have ht2 : |eA| ≤ |CA| * (Ex + Ey * (x ^ κ / y) + 1) := by
      refine hAreal.trans ?_
      have h0 : 0 ≤ Ex + Ey * (x ^ κ / y) + 1 := by positivity
      exact mul_le_mul_of_nonneg_right (le_abs_self CA) h0
    nlinarith
  have hE1 : Ex * (y / x ^ κ) = 1 / y := by
    rw [hEx]
    field_simp
  have hE2 : (x ^ κ / y) * (y / x ^ κ) = 1 := by field_simp
  have hE3 : y / x ^ κ ≤ D * (1 / y) := by
    have h1 := hDb x (by linarith)
    rw [hlogx] at h1
    rw [div_le_iff₀ hxk, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hy0]
    nlinarith
  have hyr : 0 < y / x ^ κ := by positivity
  have hone : 0 < 1 / y := by positivity
  calc |eA - e₂ - R| * (y / x ^ κ)
      ≤ ((|CA| + C₂ + C₃) * Ex + |CA| * Ey * (x ^ κ / y) + |CA|) * (y / x ^ κ) :=
        mul_le_mul_of_nonneg_right hsum hyr.le
    _ = (|CA| + C₂ + C₃) * (Ex * (y / x ^ κ)) + |CA| * Ey * ((x ^ κ / y) * (y / x ^ κ)) +
          |CA| * (y / x ^ κ) := by ring
    _ ≤ (|CA| + C₂ + C₃) * (1 / y) + |CA| * Ey * 1 + |CA| * (D * (1 / y)) := by
        rw [hE1, hE2]
        have := mul_le_mul_of_nonneg_left hE3 (abs_nonneg CA)
        linarith
    _ ≤ ((|CA| + C₂ + C₃) + |CA| * D + |CA|) * (1 / y + Ey) := by
        have h1 : 0 ≤ (|CA| + C₂ + C₃) * Ey := by positivity
        have h2 : 0 ≤ |CA| * D * Ey := by positivity
        have h3 : 0 ≤ |CA| * (1 / y) := by positivity
        nlinarith

end CpsLean
