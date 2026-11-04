module

public import CpsLean.Table1Data
public import CpsLean.LiGridData
public import CpsLean.Grid
public import CpsLean.RippleRH
public import CpsLean.Zeros
set_option autoImplicit false

/-!
# The numerical facts of the paper that are stated as such

Proved, in the kernel:
* `grid_integers`: the values of `S_N` in Sections 3–4, among them `S(4691) = 1378036`.
* `table1_primes`: the primes `N_n` of Table 1 (Lucas certificates).
* `first_crossing_table`, `first_crossing_a1`: the race `θ₁(x)` against `li(x²)` first turns at `x = 109`.

As a certificate:
* `Table1Cert`: the position of `γ_n` in its cell, `n ≤ 20`.
* `table1_crossing`: with `Table1Cert`, `N(γ_n) = N_n` for `n ≤ 20`.
-/

open Real Set

@[expose] public section

namespace CpsLean

theorem S_eq_sumLoop (N : ℕ) : S N = sumLoop (N + 1) 0 1 := by
  rw [sumLoop_eq, S, Finset.sum_filter, zero_add, Finset.range_eq_Ico]

/-- The values of `S_N` in the paper; `4691` is prime. -/
theorem grid_integers :
    S 10 = 18 ∧ S 100 = 1061 ∧ S 1000 = 76128 ∧ S 10000 = 5736397 ∧
      Nat.Prime 4691 ∧ S 4691 = 1378036 := by
  refine ⟨(S_eq_sumLoop 10).trans (by decide +kernel), (S_eq_sumLoop 100).trans (by decide +kernel),
    (S_eq_sumLoop 1000).trans (by decide +kernel), (S_eq_sumLoop 10000).trans (by decide +kernel),
    by norm_num, (S_eq_sumLoop 4691).trans (by decide +kernel)⟩

/-- `Σ_{p≤x} p = S_x − 1` in the table of Section 9.1. -/
theorem first_crossing_table :
    S 103 = 1265 ∧ S 107 = 1372 ∧ S 109 = 1481 ∧ S 112 = 1481 ∧ S 113 = 1594 ∧ S 127 = 1721 :=
  ⟨(S_eq_sumLoop 103).trans (by decide +kernel), (S_eq_sumLoop 107).trans (by decide +kernel),
    (S_eq_sumLoop 109).trans (by decide +kernel), (S_eq_sumLoop 112).trans (by decide +kernel),
    (S_eq_sumLoop 113).trans (by decide +kernel), (S_eq_sumLoop 127).trans (by decide +kernel)⟩

theorem liChain_grid : liChainOk 16 64 5000 20000 liGrid = true := by decide +kernel

theorem liGrid_bounds : ∀ e ∈ liGrid, 8 < e.1 ∧ (e.2.2.2.1 : ℝ) / 10 ^ 4 ≤ li ((e.1 : ℝ) / 8) ∧
    li ((e.1 : ℝ) / 8) ≤ (e.2.2.2.2 : ℝ) / 10 ^ 4 := by
  have hl2 := Real.log_two_gt_d9
  refine liChain_sound liGrid 16 64 5000 20000 (by norm_num) ?_ ?_ ?_ liChain_grid
  · have := li_two_bounds.1
    norm_num at this ⊢
    linarith
  · have := li_two_bounds.2
    norm_num at this ⊢
    linarith
  · norm_num at hl2 ⊢
    linarith

theorem thetaPow_one_eq_S (x : ℝ) : thetaPow 1 x = (S ⌊x⌋₊ : ℝ) - 1 := by
  unfold thetaPow S
  have e : (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime = (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    ext q
    simp
  rw [e]
  push_cast
  simp

/-- **The first crossing at `a = 1`.** On `x ≥ 2`, the least `x` with `li(x²) < θ₁(x)` is `109`. -/
theorem first_crossing_a1 :
    IsLeast {x : ℝ | 2 ≤ x ∧ li (x ^ ((1 : ℝ) + 1)) < thetaPow 1 x} 109 := by
  have hsq : ∀ x : ℝ, 0 ≤ x → x ^ ((1 : ℝ) + 1) = x ^ 2 := fun x hx => by
    rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  constructor
  · refine ⟨by norm_num, ?_⟩
    rw [hsq _ (by norm_num), thetaPow_one_eq_S]
    have hfl : ⌊(109 : ℝ)⌋₊ = 109 := Nat.floor_ofNat _
    rw [hfl]
    have hS : S 109 = 1481 := by
      rw [S_eq_sumLoop]
      decide +kernel
    obtain ⟨e, he, hb, hU⟩ : ∃ e ∈ liGrid, e.1 = 95048 ∧ e.2.2.2.2 < 14800000 := by decide +kernel
    obtain ⟨-, -, h3⟩ := liGrid_bounds e he
    rw [hb] at h3
    have hUr : (e.2.2.2.2 : ℝ) < 14800000 := by exact_mod_cast hU
    have e1 : ((95048 : ℕ) : ℝ) / 8 = 109 ^ 2 := by norm_num
    rw [e1] at h3
    rw [hS]
    push_cast
    norm_num at h3 ⊢
    linarith
  · rintro x ⟨hx2, hlt⟩
    by_contra hx
    push Not at hx
    have hx0 : 0 ≤ x := by linarith
    set n := ⌊x⌋₊ with hn
    have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
    have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx2)
    have hn109 : n < 109 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx)
    have hkey : ∀ n ∈ Finset.Ico 2 109, ∃ e ∈ liGrid, e.1 ≤ 8 * n * n ∧
        (S n - 1) * 10 ^ 4 < e.2.2.2.1 := by
      have hk : ∀ n ∈ Finset.Ico 2 109, ∃ e ∈ liGrid, e.1 ≤ 8 * n * n ∧
          (sumLoop (n + 1) 0 1 - 1) * 10 ^ 4 < e.2.2.2.1 := by decide +kernel
      intro n hn
      rw [S_eq_sumLoop]
      exact hk n hn
    obtain ⟨e, he, hb, hL⟩ := hkey n (Finset.mem_Ico.mpr ⟨hn2, hn109⟩)
    obtain ⟨h8, h2, -⟩ := liGrid_bounds e he
    rw [hsq x hx0, thetaPow_one_eq_S, ← hn] at hlt
    have hb' : (e.1 : ℝ) / 8 ≤ x ^ 2 := by
      have hbr : (e.1 : ℝ) ≤ 8 * n * n := by exact_mod_cast hb
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    have h81 : (1 : ℝ) < (e.1 : ℝ) / 8 := by
      have : (8 : ℝ) < e.1 := by exact_mod_cast h8
      linarith
    have hmono := li_mono h81 hb'
    have hS1 : 1 ≤ S n := S_pos n
    have hLr : ((S n : ℝ) - 1) * 10 ^ 4 < e.2.2.2.1 := by
      have : (((S n - 1) * 10 ^ 4 : ℕ) : ℝ) < e.2.2.2.1 := by exact_mod_cast hL
      push_cast [Nat.cast_sub hS1] at this
      norm_num at this ⊢
      exact this
    have : (S n : ℝ) - 1 < (e.2.2.2.1 : ℝ) / 10 ^ 4 := by
      rw [lt_div_iff₀ (by norm_num)]
      exact hLr
    linarith

/-- **Arb certificate of Table 1.** For each row `(n, lo, hi, N)` of `table1Rows`, `m = π(N)`: the `n`-th zero has ordinate `γ ∈ (lo/10²⁴, hi/10²⁴)`, `σ_{m−1} < lo/10²⁴`, `hi/10²⁴ ≤ σ_m`. Two points of trust: the sums `S(N_n)` come from primesum (`02_certify.py`, `run.jsonl` = Zenodo 10.5281/zenodo.23269807), rechecked by sieve for `n ≤ 5`; the index `zeroCount γ = n` comes from Arb's rigorous isolation of the zeros (`acb_dirichlet_zeta_zeros`), 400 bits. Intervals: `scripts/numerics/certify_table1.py`, output `table1_cert.txt`. A numerical certificate, taken as a hypothesis. -/
def Table1Cert : Prop :=
  ∀ r ∈ table1Rows, ∃ γ ∈ zeroOrdinates, zeroCount γ = r.1 ∧
    (r.2.1 : ℝ) / 10 ^ 24 < γ ∧ γ < (r.2.2.1 : ℝ) / 10 ^ 24 ∧
    sigma (Nat.primeCounting r.2.2.2 - 1) < (r.2.1 : ℝ) / 10 ^ 24 ∧
    (r.2.2.1 : ℝ) / 10 ^ 24 ≤ sigma (Nat.primeCounting r.2.2.2)

/-- **Table 1**, with `Table1Cert`: `σ_{m−1} < γ_n ≤ σ_m`, `m = π(N_n)`, and `N(γ_n) = N_n`, `n ≤ 20`. -/
theorem table1_crossing (h : Table1Cert) : ∀ r ∈ table1Rows, r.2.2.2.Prime ∧
    ∃ γ ∈ zeroOrdinates, zeroCount γ = r.1 ∧
      (r.2.1 : ℝ) / 10 ^ 24 < γ ∧ γ < (r.2.2.1 : ℝ) / 10 ^ 24 ∧
      sigma (Nat.primeCounting r.2.2.2 - 1) < γ ∧ γ ≤ sigma (Nat.primeCounting r.2.2.2) ∧
      firstCrossing γ = r.2.2.2 := by
  intro r hr
  have hp := table1_primes r hr
  obtain ⟨γ, hγ, hn, hlo, hhi, hm1, hm⟩ := h r hr
  refine ⟨hp, γ, hγ, hn, hlo, hhi, hm1.trans hlo, hhi.le.trans hm, ?_⟩
  set N := r.2.2.2 with hN
  have hle : γ ≤ log (S N) := by
    have := hhi.le.trans hm
    unfold sigma at this
    rwa [prime_primeCounting hp] at this
  refine le_antisymm (firstCrossing_le hp hle) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨hq, hq2⟩ := firstCrossing_mem γ
  set q := firstCrossing γ with hqdef
  -- `π(q) ≤ π(N) − 1`
  have hcount : Nat.primeCounting q + 1 ≤ Nat.primeCounting N := by
    unfold Nat.primeCounting Nat.primeCounting'
    have h1 : Nat.count Nat.Prime (q + 1) ≤ Nat.count Nat.Prime N :=
      Nat.count_monotone _ hlt
    have h2 : Nat.count Nat.Prime N < Nat.count Nat.Prime (N + 1) :=
      Nat.count_strict_mono hp (Nat.lt_succ_self N)
    omega
  have hle2 : q ≤ prime (Nat.primeCounting N - 1) := by
    have hpq := prime_primeCounting hq
    have hpos : 1 ≤ Nat.primeCounting q := by
      by_contra h0
      have h00 : Nat.primeCounting q = 0 := by omega
      rw [h00] at hpq
      -- `prime 0 = prime 1 = 2`, and `π(2) = 1`
      have h2 : q = 2 := by
        rw [← hpq]
        exact prime_one
      rw [h2] at h00
      revert h00
      decide
    calc q = prime (Nat.primeCounting q) := hpq.symm
      _ ≤ prime (Nat.primeCounting N - 1) := by
          unfold prime
          exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)
  have hS := S_mono hle2
  have hlog : log (S q) ≤ sigma (Nat.primeCounting N - 1) :=
    log_le_log (S_pos_real q) (by exact_mod_cast hS)
  linarith [hm1.trans hlo]

end CpsLean
