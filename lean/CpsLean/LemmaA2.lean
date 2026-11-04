module

public import CpsLean.LemmaA1
set_option autoImplicit false

/-!
# Lemma A, second part: the exact identities

With `v = 5/2`, `f(t) = t^a/log t` and `S = {ρ : |γ| < T}`:

* `piA_eq`:
  `Π_a(x) = 2^a + ∫_v^x f − f(v)G(v) − Σ_S ∫_v^x t^{ρ+a−1}/log t + f(x)G(x) − ∫_v^x f′G`,
  with `G = psiRem T`.
* `lInt_eq`: `∫_v^x t^{s−1}/log t = A_s(x) − A_s(v) + (2/s²) ∫_v^x t^{s−1}/log³t`, with
  `A_s(t) = t^s/(s log t) + t^s/(s² log²t)`.
-/

open Finset Real Filter Topology Asymptotics MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- `L(s; x) = ∫_{5/2}^x t^{s−1}/log t dt` (the lower limit `5/2`, see `DIVERGENZE.md`). -/
noncomputable def lInt (s : ℂ) (x : ℝ) : ℂ :=
  ∫ t in (5 / 2 : ℝ)..x, (t : ℂ) ^ (s - 1) / (log t : ℂ)

/-- `W_s(x) = ∫_{5/2}^x t^{s−1}/log³ t dt`. -/
noncomputable def wInt (s : ℂ) (x : ℝ) : ℂ :=
  ∫ t in (5 / 2 : ℝ)..x, (t : ℂ) ^ (s - 1) / (log t : ℂ) ^ 3

/-- `A_s(t) = t^s/(s log t) + t^s/(s² log² t)`. -/
noncomputable def aTerm (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ s / (s * (log t : ℂ)) + (t : ℂ) ^ s / (s ^ 2 * (log t : ℂ) ^ 2)

theorem cpow_eq_mul {s : ℂ} {t : ℝ} (ht : 0 < t) : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * t := by
  have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have h := Complex.cpow_add (s - 1) 1 hne
  rwa [sub_add_cancel, Complex.cpow_one] at h

theorem hasDerivAt_log_ofReal {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (log y : ℂ)) (((1 / t : ℝ)) : ℂ) t := by
  have := (hasDerivAt_log ht.ne').ofReal_comp
  simpa [one_div] using this

theorem hasDerivAt_aTerm {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (aTerm s)
      ((t : ℂ) ^ (s - 1) / (log t : ℂ) - 2 / s ^ 2 * ((t : ℂ) ^ (s - 1) / (log t : ℂ) ^ 3)) t := by
  have ht0 : 0 < t := by linarith
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hl : (log t : ℂ) ≠ 0 := by exact_mod_cast (log_pos ht).ne'
  have hD := hasDerivAt_ofReal_cpow_const (x := t) ht0.ne' hs
  have hL := hasDerivAt_log_ofReal ht0
  have h1 := hD.div (hL.const_mul s) (mul_ne_zero hs hl)
  have h2 := hD.div ((hL.pow 2).const_mul (s ^ 2)) (mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 2 hl))
  refine (h1.add h2).congr_deriv ?_
  rw [cpow_eq_mul ht0 (s := s)]
  simp only [Pi.pow_apply]
  push_cast
  field_simp
  ring

theorem continuousOn_cpow_div_log (s : ℂ) (k : ℕ) {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1) / (log t : ℂ) ^ k) (Set.Icc (5 / 2) x) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  have hl : (log t : ℂ) ≠ 0 := by exact_mod_cast (log_pos ht1).ne'
  have hc : ContinuousAt (fun y : ℝ => (log y : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_log ht0.ne')
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')).div (hc.pow k)
    (pow_ne_zero k hl)).continuousWithinAt

theorem intervalIntegrable_cpow_div_log (s : ℂ) (k : ℕ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) / (log t : ℂ) ^ k) volume (5 / 2) x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact continuousOn_cpow_div_log s k

/-- `∫_v^x t^{s−1}/log t = A_s(x) − A_s(v) + (2/s²) ∫_v^x t^{s−1}/log³ t`. -/
theorem lInt_eq {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 5 / 2 ≤ x) :
    lInt s x = aTerm s x - aTerm s (5 / 2) + 2 / s ^ 2 * wInt s x := by
  have h1 := intervalIntegrable_cpow_div_log s 1 hx
  have h3 := intervalIntegrable_cpow_div_log s 3 hx
  simp only [pow_one] at h1
  have hd : ∀ t ∈ uIcc (5 / 2 : ℝ) x, HasDerivAt (aTerm s)
      ((t : ℂ) ^ (s - 1) / (log t : ℂ) - 2 / s ^ 2 * ((t : ℂ) ^ (s - 1) / (log t : ℂ) ^ 3)) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact hasDerivAt_aTerm hs (by linarith [ht.1])
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.sub (h3.const_mul _))
  rw [intervalIntegral.integral_sub h1 (h3.const_mul _), intervalIntegral.integral_const_mul] at hint
  unfold lInt wInt
  rw [← hint]
  ring

theorem hasDerivAt_fw_cpow (a : ℝ) {ρ : ℂ} (hρ : ρ ≠ 0) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun y : ℝ => ((fw a y : ℝ) : ℂ) * ((y : ℂ) ^ ρ / ρ))
      (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ) + (t : ℂ) ^ (ρ + a - 1) / (log t : ℂ)) t := by
  have ht0 : 0 < t := by linarith
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hD := (hasDerivAt_ofReal_cpow_const (x := t) ht0.ne' hρ).div_const ρ
  have h := (hasDerivAt_fw a ht).ofReal_comp.mul hD
  refine h.congr_deriv ?_
  have hcpow : (t : ℂ) ^ (ρ + a - 1) = ((t ^ a : ℝ) : ℂ) * (t : ℂ) ^ (ρ - 1) := by
    rw [Complex.ofReal_cpow ht0.le, ← Complex.cpow_add _ _ htC]
    congr 1
    ring
  rw [hcpow]
  unfold fw
  push_cast
  field_simp

theorem continuousOn_cpow_div (ρ : ℂ) {x : ℝ} :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ ρ / ρ) (Set.Icc (5 / 2) x) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')).div_const ρ).continuousWithinAt

theorem continuousOn_fw'_complex (a : ℝ) {x : ℝ} :
    ContinuousOn (fun t : ℝ => ((fw' a t : ℝ) : ℂ)) (Set.Icc (5 / 2) x) :=
  Complex.continuous_ofReal.comp_continuousOn (continuousOn_fw'_five_half a)

theorem intervalIntegrable_fw'_cpow (a : ℝ) (ρ : ℂ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => ((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ)) volume (5 / 2) x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact (continuousOn_fw'_complex a).mul (continuousOn_cpow_div ρ)

/-- `∫_v^x f′ t^ρ/ρ = f(x) x^ρ/ρ − f(v) v^ρ/ρ − L(ρ + a; x)`. -/
theorem integral_fw'_cpow (a : ℝ) {ρ : ℂ} (hρ : ρ ≠ 0) {x : ℝ} (hx : 5 / 2 ≤ x) :
    ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ) =
      ((fw a x : ℝ) : ℂ) * ((x : ℂ) ^ ρ / ρ) -
        ((fw a (5 / 2) : ℝ) : ℂ) * (((5 / 2 : ℝ) : ℂ) ^ ρ / ρ) - lInt (ρ + a) x := by
  have h1 := intervalIntegrable_fw'_cpow a ρ hx
  have h2 := intervalIntegrable_cpow_div_log (ρ + a) 1 hx
  simp only [pow_one] at h2
  have hd : ∀ t ∈ uIcc (5 / 2 : ℝ) x, HasDerivAt (fun y : ℝ => ((fw a y : ℝ) : ℂ) * ((y : ℂ) ^ ρ / ρ))
      (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ) + (t : ℂ) ^ (ρ + a - 1) / (log t : ℂ)) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact hasDerivAt_fw_cpow a hρ (by linarith [ht.1])
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2] at hint
  unfold lInt
  rw [← hint]
  ring

theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => ((f t : ℝ) : ℂ)) volume a b :=
  ⟨h.1.ofReal, h.2.ofReal⟩

theorem intervalIntegrable_fw'_mul_id (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => fw' a t * t) volume (5 / 2) x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact (continuousOn_fw'_five_half a).mul continuousOn_id

theorem continuousOn_fw_five_half (a : ℝ) {x : ℝ} : ContinuousOn (fw a) (Set.Icc (5 / 2) x) :=
  (continuousOn_fw a).mono fun t ht => (by linarith [ht.1] : (2 : ℝ) ≤ t)

theorem intervalIntegrable_fw (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fw a) volume (5 / 2) x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact continuousOn_fw_five_half a

/-- `∫_v^x f′(t) t = x f(x) − v f(v) − ∫_v^x f`. -/
theorem integral_fw'_mul_id (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    ∫ t in (5 / 2 : ℝ)..x, fw' a t * t =
      x * fw a x - 5 / 2 * fw a (5 / 2) - ∫ t in (5 / 2 : ℝ)..x, fw a t := by
  have h1 := intervalIntegrable_fw'_mul_id a hx
  have h2 := intervalIntegrable_fw a hx
  have hd : ∀ t ∈ uIcc (5 / 2 : ℝ) x, HasDerivAt (fun y : ℝ => y * fw a y) (fw' a t * t + fw a t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have := (hasDerivAt_id' t).mul (hasDerivAt_fw a (by linarith [ht.1]))
    refine this.congr_deriv ?_
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2] at hint
  linarith

theorem intervalIntegrable_fw'_mul_psi (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => fw' a t * Chebyshev.psi t) volume (5 / 2) x := by
  have hc : ContinuousOn (fw' a) (Set.uIcc (5 / 2) x) := by
    rw [uIcc_of_le hx]
    exact continuousOn_fw'_five_half a
  exact (Chebyshev.psi_mono.intervalIntegrable).continuousOn_mul hc

/-- `f′ (ψ − id)`, as a complex function, is integrable. -/
theorem intervalIntegrable_fw'_mul_psi_sub (a : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => ((fw' a t : ℝ) : ℂ) * ((Chebyshev.psi t - t : ℝ) : ℂ)) volume
      (5 / 2) x := by
  have h := intervalIntegrable_ofReal
    ((intervalIntegrable_fw'_mul_psi a hx).sub (intervalIntegrable_fw'_mul_id a hx))
  refine h.congr fun t _ => ?_
  push_cast
  ring

theorem zeroZ_eq (T t : ℝ) : zeroZ T t = ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * ((t : ℂ) ^ ρ / ρ) :=
  zeroSumLt_eq _ _

theorem ne_zero_of_mem {ρ : ℂ} (h : ρ ∈ nontrivialZeros) : ρ ≠ 0 := by
  rintro rfl
  have := h.2.1
  simp at this

theorem intervalIntegrable_fw'_mul_psiRem (a T : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => ((fw' a t : ℝ) : ℂ) * psiRem T t) volume (5 / 2) x := by
  have hZ : IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ zerosLt T,
      (zeroMult ρ : ℂ) * (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ))) volume (5 / 2) x :=
    by
      have := IntervalIntegrable.sum (zerosLt T) (f := fun ρ t => (zeroMult ρ : ℂ) *
        (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ))) (μ := volume) (a := 5 / 2) (b := x)
        fun ρ _ => (intervalIntegrable_fw'_cpow a ρ hx).const_mul _
      refine this.congr fun t _ => ?_
      simp [Finset.sum_apply]
  refine ((intervalIntegrable_fw'_mul_psi_sub a hx).add hZ).congr fun t _ => ?_
  unfold psiRem
  rw [zeroZ_eq, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun ρ _ => by ring

/-- **The exact formula for `Π_a`**: with `v = 5/2`, `f(t) = t^a/log t`, `G = psiRem T`,
`Π_a(x) = 2^a + ∫_v^x f − f(v)G(v) − Σ_{|γ|<T} L(ρ + a; x) + f(x)G(x) − ∫_v^x f′G`. -/
theorem piA_eq (a T : ℝ) {x : ℝ} (hx : 5 / 2 ≤ x) :
    ((piA a x : ℝ) : ℂ) = ((2 ^ a : ℝ) : ℂ) + ((∫ t in (5 / 2 : ℝ)..x, fw a t : ℝ) : ℂ) -
        ((fw a (5 / 2) : ℝ) : ℂ) * psiRem T (5 / 2) -
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * lInt (ρ + a) x +
        ((fw a x : ℝ) : ℂ) * psiRem T x -
        ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * psiRem T t := by
  have hab := piA_abel a hx
  have e1 : ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * psiRem T t =
      ((∫ t in (5 / 2 : ℝ)..x, (fw' a t * Chebyshev.psi t - fw' a t * t) : ℝ) : ℂ) +
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
          ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ) := by
    have hZ : ∀ ρ ∈ zerosLt T, IntervalIntegrable (fun t : ℝ => (zeroMult ρ : ℂ) *
        (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ))) volume (5 / 2) x :=
      fun ρ _ => (intervalIntegrable_fw'_cpow a ρ hx).const_mul _
    have hsplit : ∀ t : ℝ, ((fw' a t : ℝ) : ℂ) * psiRem T t =
        (((fw' a t * Chebyshev.psi t - fw' a t * t : ℝ)) : ℂ) + ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
          (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ)) := by
      intro t
      unfold psiRem
      rw [zeroZ_eq, mul_add, Finset.mul_sum]
      congr 1
      · push_cast
        ring
      · exact Finset.sum_congr rfl fun ρ _ => by ring
    simp only [hsplit]
    have hr := intervalIntegrable_ofReal
      ((intervalIntegrable_fw'_mul_psi a hx).sub (intervalIntegrable_fw'_mul_id a hx))
    have hS : IntervalIntegrable (fun t : ℝ => ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
        (((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ))) volume (5 / 2) x := by
      refine (IntervalIntegrable.sum (zerosLt T) hZ).congr fun t _ => ?_
      simp [Finset.sum_apply]
    rw [intervalIntegral.integral_add hr hS,
      intervalIntegral.integral_finsetSum hZ, intervalIntegral.integral_ofReal]
    congr 1
    exact Finset.sum_congr rfl fun ρ _ => intervalIntegral.integral_const_mul _ _
  have e2 : ∫ t in (5 / 2 : ℝ)..x, (fw' a t * Chebyshev.psi t - fw' a t * t) =
      (∫ t in (5 / 2 : ℝ)..x, fw' a t * Chebyshev.psi t) -
        (x * fw a x - 5 / 2 * fw a (5 / 2) - ∫ t in (5 / 2 : ℝ)..x, fw a t) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_fw'_mul_psi a hx)
      (intervalIntegrable_fw'_mul_id a hx), integral_fw'_mul_id a hx]
  have e3 : ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) *
      ∫ t in (5 / 2 : ℝ)..x, ((fw' a t : ℝ) : ℂ) * ((t : ℂ) ^ ρ / ρ) =
      ((fw a x : ℝ) : ℂ) * zeroZ T x - ((fw a (5 / 2) : ℝ) : ℂ) * zeroZ T (5 / 2) -
        ∑ ρ ∈ zerosLt T, (zeroMult ρ : ℂ) * lInt (ρ + a) x := by
    rw [zeroZ_eq, zeroZ_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [integral_fw'_cpow a (ne_zero_of_mem (mem_zerosLt.mp hρ).1) hx]
    ring
  rw [e1, e2, e3, hab]
  unfold psiRem
  rw [psi_five_half]
  push_cast
  ring

end CpsLean
