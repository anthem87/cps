module

public import CpsLean.LemmaA3
set_option autoImplicit false

/-!
# Lemma A

`lemmaA`: **Lemma A** of the paper (the pointwise form of the layer `k = 1`), for every real
`a > −½`. Under the Riemann hypothesis, for `Y ≥ 2`, `T = e^Y`, `3 ≤ x ≤ e^Y`,
`Π_a(x) = li(x^{a+1}) − (x^κ/log x) Σ_{|γ|≤T} x^{iγ}/(ρ + a)
  + O_a(x^κ/log² x + Y² e^{−Y/2} x^κ/log x + 1)`, with `κ = a + ½`.
It uses the truncated explicit formula only for `x ≥ 5/2` (`DIVERGENZE.md`, D2).
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- The finite set of the nontrivial zeros with `|γ| ≤ T`. -/
noncomputable def zerosLe (T : ℝ) : Finset ℂ := (finite_zeros T).toFinset

theorem mem_zerosLe {T : ℝ} {ρ : ℂ} : ρ ∈ zerosLe T ↔ ρ ∈ nontrivialZeros ∧ |ρ.im| ≤ T := by
  simp [zerosLe]

theorem zeroSumLe_eq (T : ℝ) (f : ℂ → ℂ) :
    zeroSumLe T f = ∑ ρ ∈ zerosLe T, (zeroMult ρ : ℂ) * f ρ := by
  unfold zeroSumLe zerosLe
  exact finsum_mem_eq_finite_toFinset_sum _ _

/-- The finite set of the nontrivial zeros with `|γ| = T`. -/
noncomputable def zerosEq (T : ℝ) : Finset ℂ := (zerosLe T).filter (fun ρ => ¬ |ρ.im| < T)

theorem mem_zerosEq {T : ℝ} {ρ : ℂ} : ρ ∈ zerosEq T ↔ ρ ∈ nontrivialZeros ∧ |ρ.im| = T := by
  simp only [zerosEq, Finset.mem_filter, mem_zerosLe, not_lt]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨h0, le_antisymm h1 h2⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨h0, h1.le⟩, h1.ge⟩

theorem zeroSumLe_sub_zeroSumLt (T : ℝ) (f : ℂ → ℂ) :
    zeroSumLe T f - zeroSumLt T f = ∑ ρ ∈ zerosEq T, (zeroMult ρ : ℂ) * f ρ := by
  have h := Finset.sum_filter_add_sum_filter_not (zerosLe T) (fun ρ => |ρ.im| < T)
    (fun ρ => (zeroMult ρ : ℂ) * f ρ)
  have hf : (zerosLe T).filter (fun ρ => |ρ.im| < T) = zerosLt T := by
    ext ρ
    simp only [Finset.mem_filter, mem_zerosLe, mem_zerosLt]
    constructor
    · rintro ⟨⟨h0, _⟩, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩
      exact ⟨⟨h0, h2.le⟩, h2⟩
  rw [hf] at h
  rw [zeroSumLe_eq, zeroSumLt_eq, ← h]
  simp [zerosEq]

/-- `Σ_{|γ|=T} m(ρ) ≤ M √T`, for `T ≥ 1`. -/
theorem sum_zerosEq_le (h : RiemannVonMangoldt) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 1 ≤ T → ∑ ρ ∈ zerosEq T, (zeroMult ρ : ℝ) ≤ M * √T := by
  obtain ⟨C, K₀, hC, hK₀, hband⟩ := exists_bandAbs_bound h
  set M₁ : ℝ := ∑ ρ ∈ zerosLe ((K₀ : ℝ) + 1), (zeroMult ρ : ℝ) with hM₁
  have hM₁0 : 0 ≤ M₁ := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨C + M₁, by positivity, fun T hT => ?_⟩
  have hs1 : 1 ≤ √T := by
    rw [show (1 : ℝ) = √1 by simp]
    exact sqrt_le_sqrt hT
  rcases le_or_gt T ((K₀ : ℝ) + 1) with hsmall | hbig
  · have hsub : ∑ ρ ∈ zerosEq T, (zeroMult ρ : ℝ) ≤ M₁ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
      intro ρ hρ
      obtain ⟨h0, h1⟩ := mem_zerosEq.mp hρ
      exact mem_zerosLe.mpr ⟨h0, h1.le.trans hsmall⟩
    have h0 : 0 ≤ C * √T := by positivity
    nlinarith
  · set k : ℕ := ⌈T⌉₊ - 1 with hk
    have hT0 : 0 ≤ T := by linarith
    have hc1 : K₀ + 1 < ⌈T⌉₊ := by
      apply Nat.lt_ceil.mpr
      push_cast
      exact hbig
    have hcast : (k : ℝ) = (⌈T⌉₊ : ℝ) - 1 := by
      rw [hk, Nat.cast_sub (by omega)]
      simp
    have hc2 : T ≤ ⌈T⌉₊ := Nat.le_ceil _
    have hc3 : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0
    have hkK : K₀ ≤ k := by omega
    have hsub : ∑ ρ ∈ zerosEq T, (zeroMult ρ : ℝ) ≤ (zeroBandAbs (k : ℝ) ((k : ℝ) + 1) : ℝ) := by
      unfold zeroBandAbs
      rw [finsum_mem_eq_finite_toFinset_sum _ (finite_bandAbs (k : ℝ) ((k : ℝ) + 1))]
      push_cast
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
      intro ρ hρ
      obtain ⟨h0, h1⟩ := mem_zerosEq.mp hρ
      rw [Set.Finite.mem_toFinset]
      exact ⟨h0, by rw [h1]; linarith, by rw [h1]; linarith⟩
    have hkT : √(k : ℝ) ≤ √T := sqrt_le_sqrt (by linarith)
    have hb := hband k hkK
    have h1 : C * √(k : ℝ) ≤ C * √T := mul_le_mul_of_nonneg_left hkT hC
    have h0 : 0 ≤ M₁ * √T := by positivity
    nlinarith

theorem zerosLt_subset (T : ℝ) : (↑(zerosLt T) : Set ℂ) ⊆ nontrivialZeros :=
  fun _ hρ => (mem_zerosLt.mp (Finset.mem_coe.mp hρ)).1

theorem re_add_eq (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) (a : ℝ) :
    (ρ + (a : ℂ)).re = a + 1 / 2 := by
  simp [re_eq_half hRH hρ]
  ring

theorem add_ne_zero_of_mem (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) {a : ℝ}
    (ha : -1 / 2 < a) : ρ + (a : ℂ) ≠ 0 := by
  intro h
  have := re_add_eq hRH hρ a
  rw [h] at this
  simp at this
  linarith

theorem norm_cpow_add (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) (a : ℝ)
    {t : ℝ} (ht : 0 < t) : ‖(t : ℂ) ^ (ρ + (a : ℂ))‖ = t ^ (a + 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, re_add_eq hRH hρ]

/-- A finite sum over the zeros, with terms `≤ b/|ρ + a|²`. -/
theorem norm_sum_le_of_sq {a b K T : ℝ} {B : ℂ → ℂ} (hb : 0 ≤ b)
    (hK : ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℝ) / ‖ρ + (a : ℂ)‖ ^ 2 ≤ K)
    (hB : ∀ ρ ∈ zerosLt T, ‖B ρ‖ ≤ b * (1 / ‖ρ + (a : ℂ)‖ ^ 2)) :
    ‖∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * B ρ‖ ≤ b * K := by
  refine (norm_sum_le _ _).trans ?_
  have : ∑ ρ ∈ zerosLt T, ‖(zeroMult ρ : ℂ) * B ρ‖ ≤
      ∑ ρ ∈ zerosLt T, b * ((zeroMult ρ : ℝ) / ‖ρ + (a : ℂ)‖ ^ 2) := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_natCast]
    calc (zeroMult ρ : ℝ) * ‖B ρ‖ ≤ (zeroMult ρ : ℝ) * (b * (1 / ‖ρ + (a : ℂ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hB ρ hρ) (Nat.cast_nonneg _)
      _ = b * ((zeroMult ρ : ℝ) / ‖ρ + (a : ℂ)‖ ^ 2) := by ring
  rw [← Finset.mul_sum] at this
  exact this.trans (mul_le_mul_of_nonneg_left hK hb)

/-- The bound on `W_s(x)`, for `Re s = κ`. -/
theorem norm_wInt_le {s : ℂ} {κ x : ℝ} (hs : s.re = κ) (hx : 5 / 2 ≤ x) :
    ‖wInt s x‖ ≤ ∫ t in (5 / 2 : ℝ)..x, t ^ (κ - 1) / log t ^ 3 := by
  unfold wInt
  refine intervalIntegral.norm_integral_le_of_norm_le hx
    (Filter.Eventually.of_forall fun t ht => ?_) ?_
  · have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 < log t := log_pos (by linarith [ht.1])
    rw [norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_of_nonneg hl.le]
    simp [hs]
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact continuousOn_rpow_div_log_pow κ 3

/-- The lower boundary: `Σ_{|γ|<T} A_{ρ+a}(5/2) = O(1)` uniformly in `T = e^Y`. -/
theorem sum_aTerm_lower_le (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 2 ≤ Y →
      ‖∑ ρ ∈ zerosLt (exp Y), (zeroMult ρ : ℂ) * aTerm (ρ + (a : ℂ)) (5 / 2)‖ ≤ C := by
  obtain ⟨CG, hCG, hG⟩ := psiRem_le' hE
  obtain ⟨Ka, hKa⟩ := sum_zeros_le hN a
  obtain ⟨K0, hK0⟩ := sum_zeros_le hN 0
  set v : ℝ := 5 / 2 with hv
  have hv0 : 0 < v := by rw [hv]; norm_num
  set v₀ := log v with hv₀
  have hv₀0 : 0 < v₀ := log_five_half_pos
  set κ := a + 1 / 2 with hκ
  have hKa0 : 0 ≤ Ka := by
    have := hKa ∅ (by simp)
    simpa using this
  have hK00 : 0 ≤ K0 := by
    have := hK0 ∅ (by simp)
    simpa using this
  set GB := CG * (4 * v * 16 + log v + 1) with hGB
  have hlogv : 0 ≤ log v := hv₀0.le
  have hGB0 : 0 ≤ GB := by positivity
  set ZB := GB + |log 2 - v| with hZB
  refine ⟨v ^ κ / v₀ ^ 2 * Ka + v ^ a / v₀ * (ZB + |a| * (v ^ ((1 : ℝ) / 2) * ((K0 + Ka) / 2))),
    by positivity, fun Y hY => ?_⟩
  set T := exp Y with hT
  have hSa := hKa (zerosLt T) (zerosLt_subset T)
  have hS0 := hK0 (zerosLt T) (zerosLt_subset T)
  simp only [Complex.ofReal_zero, add_zero] at hS0
  -- the bound on `G(v)`, and so on `Z(v)`
  have hvY : v ≤ exp Y := by
    have := add_one_le_exp Y
    rw [hv]
    linarith
  have hGv : ‖psiRem T v‖ ≤ GB := by
    refine (hG Y v v hY hvY le_rfl le_rfl).trans (mul_le_mul_of_nonneg_left ?_ hCG)
    have := sq_exp_le (Y := Y) (by linarith)
    have hv4 : 4 * v * (Y ^ 2 * exp (-Y)) ≤ 4 * v * 16 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hZv : ‖zeroZ T v‖ ≤ ZB := by
    have hdec : zeroZ T v = psiRem T v - ((Chebyshev.psi v - v : ℝ) : ℂ) := by
      unfold psiRem
      ring
    rw [hdec]
    refine (norm_sub_le _ _).trans (add_le_add hGv ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, hv, psi_five_half]
  -- the two pieces of `A_s(v)`
  have hsplit : ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * aTerm (ρ + (a : ℂ)) v =
      ((v ^ a / v₀ : ℝ) : ℂ) * (zeroZ T v - (a : ℂ) *
          ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * ((v : ℂ) ^ ρ / (ρ * (ρ + (a : ℂ))))) +
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
          ((v : ℂ) ^ (ρ + (a : ℂ)) / ((ρ + (a : ℂ)) ^ 2 * (v₀ : ℂ) ^ 2)) := by
    rw [zeroZ_eq, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hρ' := (mem_zerosLt.mp hρ).1
    have h0 := ne_zero_of_mem hρ'
    have hs := add_ne_zero_of_mem hRH hρ' ha
    have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv0.ne'
    have hv₀C : (v₀ : ℂ) ≠ 0 := by exact_mod_cast hv₀0.ne'
    have hcp : (v : ℂ) ^ (ρ + (a : ℂ)) = (v : ℂ) ^ ρ * ((v ^ a : ℝ) : ℂ) := by
      rw [Complex.cpow_add _ _ hvC, Complex.ofReal_cpow hv0.le]
    unfold aTerm
    rw [hcp, show log v = v₀ from rfl]
    push_cast
    field_simp
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [add_comm (v ^ κ / v₀ ^ 2 * Ka)]
  refine add_le_add ?_ ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sub_le _ _).trans (add_le_add hZv ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    -- the sum with `1/(ρ s)`
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ ρ ∈ zerosLt T, ‖(zeroMult ρ : ℂ) * ((v : ℂ) ^ ρ / (ρ * (ρ + (a : ℂ))))‖ ≤
        v ^ ((1 : ℝ) / 2) * (((zeroMult ρ : ℝ) / ‖ρ‖ ^ 2 + (zeroMult ρ : ℝ) / ‖ρ + (a : ℂ)‖ ^ 2) / 2) := by
      intro ρ hρ
      have hρ' := (mem_zerosLt.mp hρ).1
      have hnorm : ‖(v : ℂ) ^ ρ‖ = v ^ ((1 : ℝ) / 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hv0, re_eq_half hRH hρ']
      rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast, hnorm]
      have hα : 0 < ‖ρ‖ := norm_pos_iff.mpr (ne_zero_of_mem hρ')
      have hβ : 0 < ‖ρ + (a : ℂ)‖ := norm_pos_iff.mpr (add_ne_zero_of_mem hRH hρ' ha)
      have hamgm : 1 / (‖ρ‖ * ‖ρ + (a : ℂ)‖) ≤ (1 / ‖ρ‖ ^ 2 + 1 / ‖ρ + (a : ℂ)‖ ^ 2) / 2 := by
        have h1 : 1 / (‖ρ‖ * ‖ρ + (a : ℂ)‖) = (1 / ‖ρ‖) * (1 / ‖ρ + (a : ℂ)‖) := by
          field_simp
        have h2 : 1 / ‖ρ‖ ^ 2 = (1 / ‖ρ‖) ^ 2 := by rw [div_pow, one_pow]
        have h3 : 1 / ‖ρ + (a : ℂ)‖ ^ 2 = (1 / ‖ρ + (a : ℂ)‖) ^ 2 := by rw [div_pow, one_pow]
        rw [h1, h2, h3]
        nlinarith [sq_nonneg (1 / ‖ρ‖ - 1 / ‖ρ + (a : ℂ)‖)]
      have hm : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _
      have hvp : 0 < v ^ ((1 : ℝ) / 2) := by positivity
      calc (zeroMult ρ : ℝ) * (v ^ ((1 : ℝ) / 2) / (‖ρ‖ * ‖ρ + (a : ℂ)‖))
          = (zeroMult ρ : ℝ) * v ^ ((1 : ℝ) / 2) * (1 / (‖ρ‖ * ‖ρ + (a : ℂ)‖)) := by ring
        _ ≤ (zeroMult ρ : ℝ) * v ^ ((1 : ℝ) / 2) * ((1 / ‖ρ‖ ^ 2 + 1 / ‖ρ + (a : ℂ)‖ ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hamgm (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (add_le_add hS0 hSa) (by norm_num)
  · refine norm_sum_le_of_sq (b := v ^ κ / v₀ ^ 2) (a := a) (K := Ka) (by positivity) hSa ?_
    intro ρ hρ
    have hρ' := (mem_zerosLt.mp hρ).1
    rw [norm_div, norm_cpow_add hRH hρ' a hv0, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hv₀0.le]
    have hβ : 0 < ‖ρ + (a : ℂ)‖ := norm_pos_iff.mpr (add_ne_zero_of_mem hRH hρ' ha)
    apply le_of_eq
    rw [← hκ]
    field_simp

/-- The exact split of the zero terms: the main term, the term `x^s/(s² log² x)`, the lower
boundary, and `W_s`. -/
theorem sum_lInt_eq (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) (T : ℝ) {x : ℝ} (hx : 3 ≤ x) :
    ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * lInt (ρ + (a : ℂ)) x =
      ((x ^ (a + 1 / 2) / log x : ℝ) : ℂ) *
          zeroSumLt T (fun ρ => (x : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ))) +
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
          ((x : ℂ) ^ (ρ + (a : ℂ)) / ((ρ + (a : ℂ)) ^ 2 * (log x : ℂ) ^ 2)) -
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * aTerm (ρ + (a : ℂ)) (5 / 2) +
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * (2 / (ρ + (a : ℂ)) ^ 2 * wInt (ρ + (a : ℂ)) x) := by
  have hx0 : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hl : (log x : ℂ) ≠ 0 := by exact_mod_cast (log_pos (by linarith : 1 < x)).ne'
  rw [zeroSumLt_eq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hρ' := (mem_zerosLt.mp hρ).1
  have hs := add_ne_zero_of_mem hRH hρ' ha
  rw [lInt_eq hs (by linarith)]
  have hsdec : ρ + (a : ℂ) = ((a + 1 / 2 : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ) := by
    apply Complex.ext
    · simp [re_eq_half hRH hρ']
      ring
    · simp
  have hcp : (x : ℂ) ^ (ρ + (a : ℂ)) =
      ((x ^ (a + 1 / 2) : ℝ) : ℂ) * (x : ℂ) ^ (Complex.I * (ρ.im : ℂ)) := by
    rw [hsdec, Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx0.le]
  unfold aTerm
  rw [hcp]
  push_cast
  field_simp

/-- **Lemma A** (pointwise form of the layer `k = 1`). Assume RH. For `a > −½`, `Y ≥ 2`, `T = e^Y`
and `3 ≤ x ≤ e^Y`,
`Π_a(x) = li(x^{a+1}) − (x^κ/log x) Σ_{|γ|≤T} x^{iγ}/(ρ + a)
  + O_a(x^κ/log² x + Y² e^{−Y/2} x^κ/log x + 1)`, with `κ = a + ½`. -/
theorem lemmaA (hE : TruncatedExplicitFormula) (hN : RiemannVonMangoldt)
    (hRH : RiemannHypothesis) {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, ∀ Y x : ℝ, 2 ≤ Y → 3 ≤ x → x ≤ exp Y →
      ‖((piA a x : ℝ) : ℂ) - (((li (x ^ (a + 1)) : ℝ) : ℂ) -
          ((x ^ (a + 1 / 2) / log x : ℝ) : ℂ) *
            zeroSumLe (exp Y) (fun ρ => (x : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ))))‖ ≤
        C * (x ^ (a + 1 / 2) / log x ^ 2 + Y ^ 2 * exp (-Y / 2) * (x ^ (a + 1 / 2) / log x) + 1) := by
  obtain ⟨CG, hCG, hG⟩ := psiRem_le' hE
  obtain ⟨C₁, hC₁, hb1⟩ := fw_mul_psiRem_le hE ha
  obtain ⟨C₂, hC₂, hb2⟩ := integral_fw'_mul_psiRem_le hE ha
  obtain ⟨C₃, hC₃, hb3⟩ := sum_aTerm_lower_le hE hN hRH ha
  obtain ⟨Ka, hKa⟩ := sum_zeros_le hN a
  obtain ⟨M, hM, hbM⟩ := sum_zerosEq_le hN
  set κ := a + 1 / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨C₄, hC₄, hW⟩ := integral_rpow_div_log_pow_le hκ0 3
  have hKa0 : 0 ≤ Ka := by
    have := hKa ∅ (by simp)
    simpa using this
  set v : ℝ := 5 / 2 with hv
  have hv1 : 1 < v := by rw [hv]; norm_num
  set c₀ : ℝ := ‖((2 ^ a - li (v ^ (a + 1)) : ℝ) : ℂ)‖ with hc₀
  set c₁ : ℝ := ‖((fw a v : ℝ) : ℂ)‖ * (CG * (4 * v * 16 + log v + 1)) with hc₁
  have hlv : 0 ≤ log v := (log_pos hv1).le
  have hv0 : 0 ≤ v := by linarith
  have hc₁0 : 0 ≤ c₁ := by positivity
  refine ⟨C₁ + C₂ + Ka + 2 * C₄ * Ka + M + c₀ + c₁ + C₃, fun Y x hY hx hxY => ?_⟩
  set T := exp Y with hT
  have hx0 : 0 < x := by linarith
  have hxv : (5 / 2 : ℝ) ≤ x := by linarith
  have hl1 : 1 < log x := one_lt_log_three.trans_le (log_le_log (by norm_num) hx)
  have hl : 0 < log x := by linarith
  have hT1 : 1 ≤ T := by
    rw [hT]
    exact one_le_exp (by linarith)
  have hT0 : 0 < T := exp_pos Y
  set Ex := x ^ κ / log x ^ 2 with hEx
  set Ey := Y ^ 2 * exp (-Y / 2) * (x ^ κ / log x) with hEy
  have hEx0 : 0 ≤ Ex := by positivity
  have hEy0 : 0 ≤ Ey := by positivity
  set P5 := ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
      ((x : ℂ) ^ (ρ + (a : ℂ)) / ((ρ + (a : ℂ)) ^ 2 * (log x : ℂ) ^ 2)) with hP5
  set PL := ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * aTerm (ρ + (a : ℂ)) (5 / 2) with hPL
  set P7 := ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * (2 / (ρ + (a : ℂ)) ^ 2 * wInt (ρ + (a : ℂ)) x)
    with hP7
  set f : ℂ → ℂ := fun ρ => (x : ℂ) ^ (Complex.I * (ρ.im : ℂ)) / (ρ + (a : ℂ)) with hf
  have hSa := hKa (zerosLt T) (zerosLt_subset T)
  -- the bounds
  have n5 : ‖P5‖ ≤ Ka * Ex := by
    have := norm_sum_le_of_sq (b := Ex) (a := a) (K := Ka) (T := T)
      (B := fun ρ => (x : ℂ) ^ (ρ + (a : ℂ)) / ((ρ + (a : ℂ)) ^ 2 * (log x : ℂ) ^ 2)) hEx0 hSa ?_
    · rw [mul_comm]
      exact this
    · intro ρ hρ
      have hρ' := (mem_zerosLt.mp hρ).1
      rw [norm_div, norm_cpow_add hRH hρ' a hx0, norm_mul, norm_pow, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hl.le]
      have hβ : 0 < ‖ρ + (a : ℂ)‖ := norm_pos_iff.mpr (add_ne_zero_of_mem hRH hρ' ha)
      apply le_of_eq
      rw [hEx, ← hκ]
      field_simp
  have n7 : ‖P7‖ ≤ 2 * C₄ * Ka * Ex := by
    have hb0 : 0 ≤ 2 * (C₄ * Ex) := by positivity
    have := norm_sum_le_of_sq (b := 2 * (C₄ * Ex)) (a := a) (K := Ka) (T := T)
      (B := fun ρ => 2 / (ρ + (a : ℂ)) ^ 2 * wInt (ρ + (a : ℂ)) x) hb0 hSa ?_
    · calc ‖P7‖ ≤ 2 * (C₄ * Ex) * Ka := this
        _ = 2 * C₄ * Ka * Ex := by ring
    · intro ρ hρ
      have hρ' := (mem_zerosLt.mp hρ).1
      have hw := (norm_wInt_le (re_add_eq hRH hρ' a) hxv).trans (hW x hx)
      have hdiv : x ^ κ / log x ^ 3 ≤ Ex := by
        rw [hEx]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [sq_nonneg (log x), pow_pos hl 2]
      have hw' : ‖wInt (ρ + (a : ℂ)) x‖ ≤ C₄ * Ex :=
        hw.trans (mul_le_mul_of_nonneg_left hdiv hC₄)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_ofNat]
      have hβ : 0 < ‖ρ + (a : ℂ)‖ := norm_pos_iff.mpr (add_ne_zero_of_mem hRH hρ' ha)
      calc 2 / ‖ρ + (a : ℂ)‖ ^ 2 * ‖wInt (ρ + (a : ℂ)) x‖
          ≤ 2 / ‖ρ + (a : ℂ)‖ ^ 2 * (C₄ * Ex) :=
            mul_le_mul_of_nonneg_left hw' (by positivity)
        _ = 2 * (C₄ * Ex) * (1 / ‖ρ + (a : ℂ)‖ ^ 2) := by ring
  have nG : ‖((fw a v : ℝ) : ℂ) * psiRem T v‖ ≤ c₁ := by
    rw [norm_mul, hc₁]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hvY : v ≤ exp Y := by
      have := add_one_le_exp Y
      rw [hv]
      linarith
    refine (hG Y v v hY hvY le_rfl le_rfl).trans (mul_le_mul_of_nonneg_left ?_ hCG)
    have := sq_exp_le (Y := Y) (by linarith)
    have hv4 : 4 * v * (Y ^ 2 * exp (-Y)) ≤ 4 * v * 16 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  -- the zeros with `|γ| = T`
  have nEq : ‖((x ^ κ / log x : ℝ) : ℂ) * (zeroSumLe T f - zeroSumLt T f)‖ ≤ M * Ey := by
    rw [zeroSumLe_sub_zeroSumLt, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsum : ‖∑ ρ ∈ zerosEq T, (zeroMult ρ : ℂ) * f ρ‖ ≤ M * exp (-Y / 2) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ ρ ∈ zerosEq T, ‖(zeroMult ρ : ℂ) * f ρ‖ ≤ (zeroMult ρ : ℝ) * (1 / T) := by
        intro ρ hρ
        obtain ⟨h0, h1⟩ := mem_zerosEq.mp hρ
        rw [norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        simp only [hf]
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
          sub_zero, rpow_zero]
        have hβ : T ≤ ‖ρ + (a : ℂ)‖ := by
          have h2 : |(ρ + (a : ℂ)).im| ≤ ‖ρ + (a : ℂ)‖ := Complex.abs_im_le_norm _
          have h3 : (ρ + (a : ℂ)).im = ρ.im := by simp
          rw [h3, h1] at h2
          exact h2
        exact one_div_le_one_div_of_le hT0 hβ
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hb := hbM T hT1
      have hsT : √T = exp (Y / 2) := by
        rw [hT, sqrt_eq_rpow, ← exp_mul]
        ring_nf
      have hTe : 1 / T = exp (-Y) := by rw [hT, exp_neg, one_div]
      have hid : exp (Y / 2) * exp (-Y) = exp (-Y / 2) := by
        rw [← exp_add]
        ring_nf
      calc (∑ ρ ∈ zerosEq T, (zeroMult ρ : ℝ)) * (1 / T) ≤ (M * √T) * (1 / T) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = M * exp (-Y / 2) := by
            rw [hsT, hTe, mul_assoc, hid]
    have hY1 : 1 ≤ Y ^ 2 := by nlinarith
    have hxk : 0 ≤ x ^ κ / log x := by positivity
    calc x ^ κ / log x * ‖∑ ρ ∈ zerosEq T, (zeroMult ρ : ℂ) * f ρ‖
        ≤ x ^ κ / log x * (M * exp (-Y / 2)) := mul_le_mul_of_nonneg_left hsum hxk
      _ ≤ x ^ κ / log x * (M * (Y ^ 2 * exp (-Y / 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hM) hxk
          nlinarith [exp_pos (-Y / 2)]
      _ = M * Ey := by rw [hEy]; ring
  -- the main term
  have hmain : ∫ t in (5 / 2 : ℝ)..x, fw a t = li (x ^ (a + 1)) - li (v ^ (a + 1)) :=
    integral_rpow_div_log_eq (by linarith) hv1 hxv
  have hid : ((piA a x : ℝ) : ℂ) - (((li (x ^ (a + 1)) : ℝ) : ℂ) -
        ((x ^ κ / log x : ℝ) : ℂ) * zeroSumLe T f) =
      ((2 ^ a - li (v ^ (a + 1)) : ℝ) : ℂ) - ((fw a v : ℝ) : ℂ) * psiRem T v - P5 + PL - P7 +
        ((fw a x : ℝ) : ℂ) * psiRem T x -
        (∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * psiRem T t) +
        ((x ^ κ / log x : ℝ) : ℂ) * (zeroSumLe T f - zeroSumLt T f) := by
    rw [piA_eq a T hxv, sum_lInt_eq hRH ha T hx, hmain]
    push_cast
    ring
  rw [hid]
  have nb1 := hb1 Y x hY hx hxY
  have nb2 := hb2 Y x hY hx hxY
  have nb3 := hb3 Y hY
  set e₀ : ℂ := ((2 ^ a - li (v ^ (a + 1)) : ℝ) : ℂ) with he₀
  set e₁ : ℂ := ((fw a v : ℝ) : ℂ) * psiRem T v with he₁
  set e₂ : ℂ := ((fw a x : ℝ) : ℂ) * psiRem T x with he₂
  set e₃ : ℂ := ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * psiRem T t with he₃
  set e₄ : ℂ := ((x ^ κ / log x : ℝ) : ℂ) * (zeroSumLe T f - zeroSumLt T f) with he₄
  have htri : ‖e₀ - e₁ - P5 + PL - P7 + e₂ - e₃ + e₄‖ ≤
      ‖e₀‖ + ‖e₁‖ + ‖P5‖ + ‖PL‖ + ‖P7‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ := by
    have h1 := norm_add_le (e₀ - e₁ - P5 + PL - P7 + e₂ - e₃) e₄
    have h2 := norm_sub_le (e₀ - e₁ - P5 + PL - P7 + e₂) e₃
    have h3 := norm_add_le (e₀ - e₁ - P5 + PL - P7) e₂
    have h4 := norm_sub_le (e₀ - e₁ - P5 + PL) P7
    have h5 := norm_add_le (e₀ - e₁ - P5) PL
    have h6 := norm_sub_le (e₀ - e₁) P5
    have h7 := norm_sub_le e₀ e₁
    linarith
  refine htri.trans ?_
  have h4 : 0 ≤ C₄ * Ka := by positivity
  have hfin : ‖e₀‖ + ‖e₁‖ + ‖P5‖ + ‖PL‖ + ‖P7‖ + ‖e₂‖ + ‖e₃‖ + ‖e₄‖ ≤
      c₀ + c₁ + Ka * Ex + C₃ + 2 * C₄ * Ka * Ex + C₁ * (Ex + Ey) + C₂ * (Ex + Ey) + M * Ey := by
    have : ‖e₀‖ = c₀ := rfl
    linarith
  refine hfin.trans ?_
  have hc₀0 : 0 ≤ c₀ := norm_nonneg _
  have e : (C₁ + C₂ + Ka + 2 * C₄ * Ka + M + c₀ + c₁ + C₃) * (Ex + Ey + 1) =
      c₀ + c₁ + Ka * Ex + C₃ + 2 * C₄ * Ka * Ex + C₁ * (Ex + Ey) + C₂ * (Ex + Ey) + M * Ey +
      (C₁ + C₂ + M + Ka * Ey + 2 * C₄ * Ka * Ey + M * Ex + c₀ * (Ex + Ey) + c₁ * (Ex + Ey) +
        C₃ * (Ex + Ey) + Ka + 2 * C₄ * Ka) := by ring
  rw [e]
  have : 0 ≤ C₁ + C₂ + M + Ka * Ey + 2 * C₄ * Ka * Ey + M * Ex + c₀ * (Ex + Ey) + c₁ * (Ex + Ey) +
      C₃ * (Ex + Ey) + Ka + 2 * C₄ * Ka := by positivity
  linarith

end CpsLean
