module

public import CpsLean.Step4
set_option autoImplicit false

/-!
# Enumerating the positive ordinates

* `zeroMult_pos`: a nontrivial zero has multiplicity at least `1`.
* `exists_ordinate_gt`: from Riemann–von Mangoldt, the positive ordinates are unbounded.
* `exists_ordinate_enum`: an increasing enumeration `λ : ℕ → ℝ` of the positive ordinates.
-/

open Filter Topology Asymptotics Real
open scoped ComplexConjugate

@[expose] public section

namespace CpsLean

theorem zeroMult_pos {ρ : ℂ} (hρ : ρ ∈ nontrivialZeros) : 1 ≤ zeroMult ρ := by
  have h1 := ne_one_of_mem hρ
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta _ h1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hρ.1
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h0 := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
      (show ρ ∈ ({1}ᶜ : Set ℂ) from h1) htop
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
    exact riemannZeta_ne_zero_of_one_le_re (s := 2) (by simp) (h0 h2)
  have hcast := Nat.cast_analyticOrderNatAt hnetop
  unfold zeroMult
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rw [h] at hcast
  exact hne0 (by simpa using hcast.symm)

theorem finite_ordinates_le (T : ℝ) : {γ : ℝ | γ ∈ zeroOrdinates ∧ γ ≤ T}.Finite := by
  refine ((finite_zeros (|T|)).image Complex.im).subset ?_
  rintro γ ⟨⟨hγ, ρ, hρ, rfl⟩, hT⟩
  refine ⟨ρ, ⟨hρ, ?_⟩, rfl⟩
  rw [abs_of_pos hγ]
  exact hT.trans (le_abs_self T)

/-- **The positive ordinates are unbounded**, from the Riemann–von Mangoldt formula. -/
theorem exists_ordinate_gt (h : RiemannVonMangoldt) (B : ℝ) : ∃ γ ∈ zeroOrdinates, B < γ := by
  by_contra hcon
  push Not at hcon
  -- beyond `B₀ = max B 0`, there are no zeros
  set B₀ := max B 0 with hB₀
  have hB₀0 : 0 ≤ B₀ := le_max_right _ _
  have hconst : ∀ T : ℝ, B₀ ≤ T → zeroCount T = zeroCount B₀ := by
    intro T hT
    rw [zeroCount_add hB₀0 hT]
    have : zeroBand B₀ T = 0 := by
      unfold zeroBand
      have hempty : {ρ : ℂ | ρ ∈ nontrivialZeros ∧ B₀ < ρ.im ∧ ρ.im ≤ T} = ∅ := by
        ext ρ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
        intro h0 h1
        have hpos : 0 < ρ.im := hB₀0.trans_lt h1
        have := hcon ρ.im ⟨hpos, ρ, h0, rfl⟩
        have hB : B ≤ B₀ := le_max_left _ _
        linarith
      rw [hempty]
      simp
    omega
  -- then `F(T) = O(log T)`, which is false
  have hF : (fun T : ℝ => T / (2 * π) * log (T / (2 * π)) - T / (2 * π)) =O[atTop]
      (fun T : ℝ => log T) := by
    have hc : (fun T : ℝ => (zeroCount T : ℝ)) =O[atTop] (fun T : ℝ => log T) := by
      refine IsBigO.of_bound (zeroCount B₀ : ℝ) ?_
      filter_upwards [eventually_ge_atTop B₀, tendsto_log_atTop.eventually_ge_atTop 1] with T hT hl
      rw [hconst T hT, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by linarith)]
      have : (0 : ℝ) ≤ zeroCount B₀ := Nat.cast_nonneg _
      nlinarith
    refine (hc.sub h).congr' ?_ EventuallyEq.rfl
    filter_upwards with T
    ring
  obtain ⟨C, hC⟩ := hF.bound
  have hpi : 0 < 2 * π := by positivity
  -- for large `T`: `F(T) ≥ T/(2π)`, and `T/(2π) > |C| log T`
  have hlo : (fun T : ℝ => log T) =o[atTop] (fun T : ℝ => T) := isLittleO_log_id_atTop
  have hsmall := hlo.def (show 0 < 1 / (2 * π * (|C| + 1)) by positivity)
  have hlogT : Tendsto (fun T : ℝ => log (T / (2 * π))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_id.atTop_div_const hpi)
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := (hC.and (hsmall.and ((hlogT.eventually_ge_atTop 2).and
    (eventually_gt_atTop (1 : ℝ))))).exists
  have hT0 : 0 < T := by linarith
  have hlT : 0 < log T := log_pos hT4
  rw [Real.norm_of_nonneg hlT.le] at hT1
  rw [Real.norm_of_nonneg hlT.le, Real.norm_of_nonneg hT0.le] at hT2
  have hF2 : T / (2 * π) ≤ T / (2 * π) * log (T / (2 * π)) - T / (2 * π) := by
    have hq : 0 < T / (2 * π) := by positivity
    nlinarith
  have hn : ‖T / (2 * π) * log (T / (2 * π)) - T / (2 * π)‖ ≥ T / (2 * π) := by
    rw [Real.norm_eq_abs]
    exact hF2.trans (le_abs_self _)
  have hup : C * log T ≤ |C| * log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlT.le
  have hq : (|C| + 1) * log T ≤ T / (2 * π) := by
    have h3 : log T * (2 * π * (|C| + 1)) ≤ T := by
      have hp : 0 < 2 * π * (|C| + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hT2 hp.le
      have e : 1 / (2 * π * (|C| + 1)) * T * (2 * π * (|C| + 1)) = T := by
        field_simp
      linarith
    rw [le_div_iff₀ hpi]
    nlinarith
  linarith

/-- For every `t` there is a least positive ordinate above `t`. -/
theorem exists_next_ordinate (h : RiemannVonMangoldt) (t : ℝ) :
    ∃ s ∈ zeroOrdinates, t < s ∧ ∀ s' ∈ zeroOrdinates, t < s' → s ≤ s' := by
  obtain ⟨γ₀, hγ₀, htγ⟩ := exists_ordinate_gt h t
  have hfin : ({γ : ℝ | γ ∈ zeroOrdinates ∧ γ ≤ γ₀} ∩ {γ | t < γ}).Finite :=
    (finite_ordinates_le γ₀).inter_of_left _
  have hne : ({γ : ℝ | γ ∈ zeroOrdinates ∧ γ ≤ γ₀} ∩ {γ | t < γ}).Nonempty :=
    ⟨γ₀, ⟨hγ₀, le_rfl⟩, htγ⟩
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image _ id hfin hne
  refine ⟨s, hs.1.1, hs.2, fun s' hs' hts' => ?_⟩
  rcases le_total s' γ₀ with hle | hle
  · exact hmin s' ⟨⟨hs', hle⟩, hts'⟩
  · exact hs.1.2.trans hle

/-- **An increasing enumeration of the positive ordinates.** -/
theorem exists_ordinate_enum (h : RiemannVonMangoldt) :
    ∃ lam : ℕ → ℝ, StrictMono lam ∧ (∀ n, 0 < lam n) ∧ Set.range lam = zeroOrdinates ∧
      Tendsto lam atTop atTop := by
  classical
  choose next hnS hnlt hnmin using exists_next_ordinate h
  let lam : ℕ → ℝ := fun n => Nat.rec (next 0) (fun _ r => next r) n
  have hlam0 : lam 0 = next 0 := rfl
  have hlams : ∀ n, lam (n + 1) = next (lam n) := fun n => rfl
  have hmem : ∀ n, lam n ∈ zeroOrdinates := by
    intro n
    cases n with
    | zero => exact hnS 0
    | succ n => exact hnS _
  have hmono : StrictMono lam := strictMono_nat_of_lt_succ fun n => by
    rw [hlams]
    exact hnlt _
  have hpos : ∀ n, 0 < lam n := fun n => (hmem n).1
  have hrange : Set.range lam = zeroOrdinates := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨n, rfl⟩
      exact hmem n
    · intro γ hγ
      by_contra hne
      have hall : ∀ n, lam n < γ := by
        intro n
        induction n with
        | zero =>
          refine lt_of_le_of_ne (hnmin 0 γ hγ hγ.1) fun heq => hne ⟨0, heq⟩
        | succ n ih =>
          refine lt_of_le_of_ne ?_ fun heq => hne ⟨n + 1, heq⟩
          rw [hlams]
          exact hnmin _ γ hγ ih
      have hfin : (Set.range lam).Finite :=
        (finite_ordinates_le γ).subset (by
          rintro _ ⟨n, rfl⟩
          exact ⟨hmem n, (hall n).le⟩)
      exact (Set.infinite_range_of_injective hmono.injective) hfin
  refine ⟨lam, hmono, hpos, hrange, ?_⟩
  refine tendsto_atTop_atTop_of_monotone hmono.monotone fun B => ?_
  obtain ⟨γ, hγ, hBγ⟩ := exists_ordinate_gt h B
  rw [← hrange] at hγ
  obtain ⟨n, rfl⟩ := hγ
  exact ⟨n, hBγ.le⟩

end CpsLean
