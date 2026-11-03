module

public import LeanBase.PrimeSums
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

/-!
# The grid of prime sums (Sections 2–3 of the paper)

Definitions 1 and 2, Proposition 1, Theorem 2 (Covering Theorem) without its asymptotic part, and
the Remark on Brown's criterion. Indices are those of the paper: `p₁ = 2`.

* `prime m = p_m`, `S N = 1 + Σ_{p ≤ N} p`, `sigma m = σ_m = log S_{p_m}`, `step m = Δ_m`.
* `firstCrossing t = N(t) = min{p prime : log S_p ≥ t}`, `eps t = ε(t) = log S_{N(t)} − t`.
* `cellIndex t = m(t)`, the index of the first-crossing prime (`p_{m(t)} = N(t)`), and
  `cell t = δ(t) = σ_{m(t)} − σ_{m(t)−1}`.
* `prime_eq_leanBase`, `S_eq_leanBase`: the bridge to `LeanBase.PrimeSums`, where `p 0 = 2`.
-/

open Finset Real

@[expose] public section

namespace CpsLean

/-- `p_m`, the `m`-th prime, with `p₁ = 2` (Definition 1). -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- `S_N = 1 + Σ_{p ≤ N} p` (Definition 1). -/
def S (N : ℕ) : ℕ := 1 + ∑ q ∈ (range (N + 1)).filter Nat.Prime, q

/-- `σ_m = log S_{p_m}` (Definition 1). -/
noncomputable def sigma (m : ℕ) : ℝ := log (S (prime m))

/-- The step `Δ_m = σ_{m+1} − σ_m` (Section 3). -/
noncomputable def step (m : ℕ) : ℝ := sigma (m + 1) - sigma m

/-- The first-crossing prime `N(t) = min{p prime : log S_p ≥ t}` (Definition 2, for `t ≥ log 3`). -/
noncomputable def firstCrossing (t : ℝ) : ℕ := sInf {p : ℕ | p.Prime ∧ t ≤ log (S p)}

/-- `ε(t) = log S_{N(t)} − t` (Definition 2). -/
noncomputable def eps (t : ℝ) : ℝ := log (S (firstCrossing t)) - t

/-- `m(t)`, the index of the first-crossing prime: `p_{m(t)} = N(t)` (Section 3). -/
noncomputable def cellIndex (t : ℝ) : ℕ := Nat.primeCounting (firstCrossing t)

/-- The width of the cell containing `t`, `δ(t) = σ_{m(t)} − σ_{m(t)−1}` (Section 3). -/
noncomputable def cell (t : ℝ) : ℝ := sigma (cellIndex t) - sigma (cellIndex t - 1)

/-! ### The bridge to `LeanBase.PrimeSums` -/

theorem prime_eq_leanBase (m : ℕ) : prime m = LeanBase.PrimeSums.p (m - 1) := rfl

theorem S_eq_leanBase (N : ℕ) : S N = LeanBase.PrimeSums.S N := rfl

theorem prime_succ (k : ℕ) : prime (k + 1) = LeanBase.PrimeSums.p k := by
  simp [prime_eq_leanBase]

/-! ### Elementary properties of `S` -/

theorem S_pos (N : ℕ) : 0 < S N := by unfold S; omega

theorem S_pos_real (N : ℕ) : (0 : ℝ) < S N := by exact_mod_cast S_pos N

theorem S_one : S 1 = 1 := by decide

theorem S_two : S 2 = 3 := by decide

theorem S_succ_of_prime {N : ℕ} (h : (N + 1).Prime) : S (N + 1) = S N + (N + 1) := by
  unfold S
  rw [range_add_one, filter_insert, if_pos h, sum_insert (by simp)]
  ring

theorem S_succ_of_not_prime {N : ℕ} (h : ¬ (N + 1).Prime) : S (N + 1) = S N := by
  unfold S
  rw [range_add_one, filter_insert, if_neg h]

theorem S_mono : Monotone S := by
  intro a b hab
  unfold S
  have : (range (a + 1)).filter Nat.Prime ⊆ (range (b + 1)).filter Nat.Prime :=
    filter_subset_filter _ (range_subset_range.2 (by omega))
  have := sum_le_sum_of_subset (f := fun q : ℕ => q) this
  omega

theorem lt_S_of_prime {q : ℕ} (hq : q.Prime) : q < S q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  rw [S_succ_of_prime hq]
  have := S_pos k
  omega

/-- For every `t` there is a prime `q` with `t ≤ log S_q`. -/
theorem exists_prime_le_log_S (t : ℝ) : ∃ q : ℕ, q.Prime ∧ t ≤ log (S q) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes ⌈exp t⌉₊
  refine ⟨q, hqp, ?_⟩
  have h1 : exp t ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hq)
  have h2 : (q : ℝ) ≤ S q := by exact_mod_cast (lt_S_of_prime hqp).le
  calc t = log (exp t) := (log_exp t).symm
    _ ≤ log (S q) := log_le_log (exp_pos t) (h1.trans h2)

/-! ### Primes and indices -/

theorem prime_prime {m : ℕ} : (prime m).Prime := Nat.prime_nth_prime _

theorem prime_one : prime 1 = 2 := Nat.nth_prime_zero_eq_two

theorem prime_two : prime 2 = 3 := Nat.nth_prime_one_eq_three

/-- `S_{p_{m+1}} = S_{p_m} + p_{m+1}` for `m ≥ 1`. -/
theorem S_prime_succ {m : ℕ} (hm : 1 ≤ m) : S (prime (m + 1)) = S (prime m) + prime (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [prime_succ, prime_succ, S_eq_leanBase, S_eq_leanBase, LeanBase.PrimeSums.S_succ]

theorem prime_lt_succ {m : ℕ} (hm : 1 ≤ m) : prime m < prime (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [prime_succ, prime_succ]; exact LeanBase.PrimeSums.p_lt_succ k

/-- For a prime `q`, `p_{π(q)} = q`. -/
theorem prime_primeCounting {q : ℕ} (hq : q.Prime) : prime (Nat.primeCounting q) = q := by
  unfold prime Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ, if_pos hq, Nat.add_sub_cancel]
  exact Nat.nth_count hq

/-! ### Definition 1: the grid is strictly increasing -/

theorem sigma_lt_succ {m : ℕ} (hm : 1 ≤ m) : sigma m < sigma (m + 1) := by
  unfold sigma
  apply log_lt_log (S_pos_real _)
  rw [S_prime_succ hm]; push_cast
  have := (prime_prime (m := m + 1)).pos
  have : (0 : ℝ) < prime (m + 1) := by exact_mod_cast this
  linarith

/-- **Definition 1.** `(σ_m)` is strictly increasing and `σ₁ = log 3`. -/
theorem def1_sigma : (∀ m n : ℕ, 1 ≤ m → m < n → sigma m < sigma n) ∧ sigma 1 = log 3 := by
  refine ⟨fun m n hm hmn => ?_, by simp [sigma, prime_one, S_two]⟩
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
    · exact (ih h).trans (sigma_lt_succ (by omega))
    · subst h; exact sigma_lt_succ hm

/-! ### Proposition 1 -/

theorem firstCrossing_mem (t : ℝ) :
    (firstCrossing t).Prime ∧ t ≤ log (S (firstCrossing t)) := by
  obtain ⟨q, hq⟩ := exists_prime_le_log_S t
  exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ t ≤ log (S p)}) ⟨q, hq⟩

theorem firstCrossing_le {t : ℝ} {q : ℕ} (hq : q.Prime) (h : t ≤ log (S q)) :
    firstCrossing t ≤ q :=
  Nat.sInf_le ⟨hq, h⟩

/-- **Proposition 1** (in the reading of its proof, see DIVERGENZE.md, D1). For `t ≥ log 3`, the first
`N ≥ 1` with `log S_N ≥ t` is the first-crossing prime `N(t)`, and `N(t)` is prime. -/
theorem prop1_crossing_prime {t : ℝ} (ht : log 3 ≤ t) :
    firstCrossing t = sInf {N : ℕ | 1 ≤ N ∧ t ≤ log (S N)} ∧ (firstCrossing t).Prime := by
  set A := {N : ℕ | 1 ≤ N ∧ t ≤ log (S N)} with hA
  obtain ⟨hNp, hNt⟩ := firstCrossing_mem t
  have hne : A.Nonempty := ⟨firstCrossing t, hNp.one_le, hNt⟩
  have hM : sInf A ∈ A := Nat.sInf_mem hne
  have h3 : (0 : ℝ) < log 3 := log_pos (by norm_num)
  have hM1 : sInf A ≠ 1 := by
    intro h
    have := hM.2; rw [h, S_one] at this; simp at this; linarith
  have hMp : (sInf A).Prime := by
    by_contra hnp
    obtain ⟨k, hk⟩ : ∃ k, sInf A = k + 1 := ⟨sInf A - 1, by have := hM.1; omega⟩
    have hk1 : 1 ≤ k := by omega
    have hmem : k ∈ A := by
      refine ⟨hk1, ?_⟩
      have := hM.2
      rwa [hk, S_succ_of_not_prime (hk ▸ hnp)] at this
    have := Nat.sInf_le hmem
    omega
  refine ⟨le_antisymm (firstCrossing_le hMp hM.2) (Nat.sInf_le ⟨hNp.one_le, hNt⟩), hNp⟩

/-! ### Theorem 2 (Covering Theorem) -/

/-- `p_{k+2} < 2 p_{k+1} ≤ S_{p_{k+1}}` and `p_{k+1} ≤ S_{p_k}` (in `LeanBase` indices). -/
theorem covering_aux (k : ℕ) :
    LeanBase.PrimeSums.p (k + 1) ≤ S (LeanBase.PrimeSums.p k) ∧
      LeanBase.PrimeSums.p (k + 2) < S (LeanBase.PrimeSums.p (k + 1)) := by
  induction k with
  | zero =>
    have h0 : LeanBase.PrimeSums.p 0 = 2 := Nat.nth_prime_zero_eq_two
    have h1 : LeanBase.PrimeSums.p 1 = 3 := Nat.nth_prime_one_eq_three
    have hlt := LeanBase.PrimeSums.p_succ_lt 1
    refine ⟨by rw [h0, h1, S_two], ?_⟩
    rw [S_eq_leanBase, LeanBase.PrimeSums.S_succ, ← S_eq_leanBase, h0, h1, S_two]
    rw [h1] at hlt; omega
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring]
    refine ⟨ih.2.le, ?_⟩
    have hlt := LeanBase.PrimeSums.p_succ_lt (k + 2)
    have hS := LeanBase.PrimeSums.S_succ (k + 1)
    rw [show k + 2 + 1 = k + 3 by ring] at hlt
    rw [show k + 1 + 1 = k + 2 by ring] at hS
    rw [S_eq_leanBase, hS, ← S_eq_leanBase]
    have := ih.2
    omega

/-- **Theorem 2(a).** `S_{p_m} ≥ p_{m+1}` for every `m ≥ 1`. -/
theorem theorem2_a {m : ℕ} (hm : 1 ≤ m) : prime (m + 1) ≤ S (prime m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [prime_succ, prime_succ]; exact (covering_aux k).1

/-- `S_{p_m} > p_{m+1}` for every `m ≥ 2`. -/
theorem theorem2_strict {m : ℕ} (hm : 2 ≤ m) : prime (m + 1) < S (prime m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [show k + 2 + 1 = (k + 1) + 1 + 1 by ring, prime_succ, prime_succ]
  exact (covering_aux k).2

/-- `Δ_m = log(1 + p_{m+1}/S_{p_m})` for `m ≥ 1`. -/
theorem step_eq {m : ℕ} (hm : 1 ≤ m) : step m = log (1 + prime (m + 1) / (S (prime m) : ℝ)) := by
  unfold step sigma
  have hS := S_pos_real (prime m)
  rw [← log_div (S_pos_real _).ne' hS.ne', S_prime_succ hm]
  congr 1; push_cast; field_simp

/-- **Theorem 2(b).** `Δ_m ≤ log 2` for `m ≥ 1`, with equality only for `m = 1`. -/
theorem theorem2_b {m : ℕ} (hm : 1 ≤ m) : step m ≤ log 2 ∧ (step m = log 2 ↔ m = 1) := by
  have hS := S_pos_real (prime m)
  have hp : (0 : ℝ) ≤ prime (m + 1) := Nat.cast_nonneg _
  have hu : (prime (m + 1) : ℝ) / S (prime m) ≤ 1 := by
    rw [div_le_one hS]; exact_mod_cast theorem2_a hm
  have hpos : (0 : ℝ) < 1 + prime (m + 1) / (S (prime m) : ℝ) := by positivity
  rw [step_eq hm]
  refine ⟨log_le_log hpos (by linarith), ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hm1
    have hlt : (prime (m + 1) : ℝ) / S (prime m) < 1 := by
      rw [div_lt_one hS]; exact_mod_cast theorem2_strict (by omega)
    have := log_lt_log hpos (show 1 + (prime (m + 1) : ℝ) / S (prime m) < 2 by linarith)
    linarith
  · subst h
    rw [prime_two, prime_one, S_two]; norm_num

theorem firstCrossing_log_three : firstCrossing (log 3) = 2 := by
  refine le_antisymm (firstCrossing_le Nat.prime_two (by rw [S_two]; norm_num)) ?_
  exact (firstCrossing_mem _).1.two_le

/-- **Theorem 2(c).** `ε(log 3) = 0`. -/
theorem theorem2_c : eps (log 3) = 0 := by
  rw [eps, firstCrossing_log_three, S_two]; push_cast; ring

/-- The cell of `t > log 3`: `m(t) ≥ 2`, `p_{m(t)} = N(t)` and `σ_{m(t)−1} < t ≤ σ_{m(t)}`. -/
theorem cell_bracket {t : ℝ} (ht : log 3 < t) :
    2 ≤ cellIndex t ∧ prime (cellIndex t) = firstCrossing t ∧
      sigma (cellIndex t - 1) < t ∧ t ≤ sigma (cellIndex t) := by
  obtain ⟨hNp, hNt⟩ := firstCrossing_mem t
  have hpm : prime (cellIndex t) = firstCrossing t := prime_primeCounting hNp
  have hN2 : firstCrossing t ≠ 2 := by
    intro h; rw [h, S_two] at hNt; push_cast at hNt; linarith
  have hm2 : 2 ≤ cellIndex t := by
    by_contra h
    have hle : cellIndex t ≤ 1 := by omega
    have : prime (cellIndex t) = 2 := by
      unfold prime; rw [show cellIndex t - 1 = 0 by omega]; exact Nat.nth_prime_zero_eq_two
    exact hN2 (hpm ▸ this)
  refine ⟨hm2, hpm, ?_, by rw [sigma, hpm]; exact hNt⟩
  by_contra h
  push Not at h
  have hlt : prime (cellIndex t - 1) < prime (cellIndex t) := by
    have := prime_lt_succ (m := cellIndex t - 1) (by omega)
    rwa [show cellIndex t - 1 + 1 = cellIndex t by omega] at this
  have := firstCrossing_le prime_prime h
  rw [hpm] at hlt
  omega

/-- **Theorem 2(d).** For every `t > log 3`, `0 ≤ ε(t) < δ(t) ≤ log 2`. -/
theorem theorem2_d {t : ℝ} (ht : log 3 < t) : 0 ≤ eps t ∧ eps t < cell t ∧ cell t ≤ log 2 := by
  obtain ⟨hm2, hpm, hlo, hhi⟩ := cell_bracket ht
  have he : eps t = sigma (cellIndex t) - t := by rw [eps, sigma, hpm]
  have hc : cell t = step (cellIndex t - 1) := by
    rw [cell, step, show cellIndex t - 1 + 1 = cellIndex t by omega]
  refine ⟨by rw [he]; linarith, by rw [he, cell]; linarith, ?_⟩
  rw [hc]; exact (theorem2_b (by omega)).1

/-- **Theorem 2** (Covering Theorem), the part that does not use the prime number theorem:
`S_{p_m} ≥ p_{m+1}` for `m ≥ 1`; `Δ_m ≤ log 2`, with equality only for `m = 1`; `ε(log 3) = 0`; and
`0 ≤ ε(t) < δ(t) ≤ log 2` for every `t > log 3`. -/
theorem theorem2_covering :
    (∀ m : ℕ, 1 ≤ m → prime (m + 1) ≤ S (prime m)) ∧
      (∀ m : ℕ, 1 ≤ m → step m ≤ log 2 ∧ (step m = log 2 ↔ m = 1)) ∧
      eps (log 3) = 0 ∧
      (∀ t : ℝ, log 3 < t → 0 ≤ eps t ∧ eps t < cell t ∧ cell t ≤ log 2) :=
  ⟨fun _ hm => theorem2_a hm, fun _ hm => theorem2_b hm, theorem2_c, fun _ ht => theorem2_d ht⟩

/-! ### The Remark on Brown's criterion -/

/-- `{1} ∪ {q prime : q ≤ p_m}`: the elements `1, 2, 3, 5, …, p_m`. -/
def gridSet (N : ℕ) : Finset ℕ := insert 1 ((range (N + 1)).filter Nat.Prime)

theorem brown_aux (k : ℕ) : ∀ T ≤ S (LeanBase.PrimeSums.p k),
    ∃ A ⊆ gridSet (LeanBase.PrimeSums.p k), ∑ a ∈ A, a = T := by
  induction k with
  | zero =>
    intro T hT
    have h0 : LeanBase.PrimeSums.p 0 = 2 := Nat.nth_prime_zero_eq_two
    rw [h0, S_two] at hT; rw [h0]
    interval_cases T
    · exact ⟨∅, empty_subset _, rfl⟩
    · exact ⟨{1}, by decide, rfl⟩
    · exact ⟨{2}, by decide, rfl⟩
    · exact ⟨{1, 2}, by decide, rfl⟩
  | succ k ih =>
    intro T hT
    set q := LeanBase.PrimeSums.p (k + 1) with hq
    have hset : gridSet q = insert q (gridSet (LeanBase.PrimeSums.p k)) := by
      unfold gridSet
      rw [range_add_one, filter_insert, if_pos (LeanBase.PrimeSums.p_prime (k + 1)),
        LeanBase.PrimeSums.primes_lt_succ, Finset.insert_comm]
    have hnot : q ∉ gridSet (LeanBase.PrimeSums.p k) := by
      unfold gridSet
      have h2 := (LeanBase.PrimeSums.p_prime (k + 1)).two_le
      have hlt := LeanBase.PrimeSums.p_lt_succ k
      simp only [mem_insert, mem_filter, mem_range]
      omega
    have hS : S q = S (LeanBase.PrimeSums.p k) + q := by
      rw [S_eq_leanBase, LeanBase.PrimeSums.S_succ, ← S_eq_leanBase]
    by_cases hTk : T ≤ S (LeanBase.PrimeSums.p k)
    · obtain ⟨A, hA, hsum⟩ := ih T hTk
      exact ⟨A, hA.trans (hset ▸ subset_insert _ _), hsum⟩
    · have hqS := (covering_aux k).1
      obtain ⟨A, hA, hsum⟩ := ih (T - q) (by omega)
      refine ⟨insert q A, ?_, ?_⟩
      · rw [hset]; exact insert_subset_insert _ hA
      · rw [sum_insert (fun h => hnot (hA h)), hsum]; omega

/-- **Remark (Brown's criterion), after Theorem 2.** For `m ≥ 1`, `p_{m+1} ≤ S_{p_m} + 1` (Brown's
criterion for `1, 2, 3, 5, …`), and every integer `T` with `1 ≤ T ≤ S_{p_m}` is a sum of distinct
elements of `{1, 2, 3, 5, …, p_m}`. -/
theorem brown_remark {m : ℕ} (hm : 1 ≤ m) :
    prime (m + 1) ≤ S (prime m) + 1 ∧
      ∀ T : ℕ, 1 ≤ T → T ≤ S (prime m) → ∃ A ⊆ gridSet (prime m), ∑ a ∈ A, a = T := by
  refine ⟨(theorem2_a hm).trans (Nat.le_succ _), fun T _ hT => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [prime_succ] at hT ⊢
  exact brown_aux k T hT

end CpsLean
