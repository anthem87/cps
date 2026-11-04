module

public import CpsLean.LemmaA
set_option autoImplicit false

/-!
# Theorem 3, Step 3: the layers `k ≥ 3`

* `layersR a x = R(x) = Σ_{3≤k≤log₂x} (1/k) θ_{ka}(x^{1/k})`.
* `piA_eq_layers`: `Π_a(x) = θ_a(x) + ½ θ_{2a}(√x) + R(x)`.
* `layersR_le`: `0 ≤ R(x) ≤ C x^{a+½}/log² x` for `x ≥ 3`, for every real `a > −½`.
* `step3_layers`: **Theorem 3, Step 3**: `R = o(x^{a+½}/log x)`.
-/

open Finset Real Filter Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt

@[expose] public section

namespace CpsLean

/-- `R(x) = Σ_{k≥3} (1/k) θ_{ka}(x^{1/k})`: for `k > log₂ x` the sum `θ_{ka}(x^{1/k})` is empty. -/
noncomputable def layersR (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 ⌊log x / log 2⌋₊, (1 / (k : ℝ)) * thetaPow (k * a) (x ^ ((1 : ℝ) / k))

theorem thetaPow_eq_Ioc (b y : ℝ) :
    thetaPow b y = ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ b := by
  unfold thetaPow
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, h⟩, hp⟩
    exact ⟨⟨hp.pos, h⟩, hp⟩
  · rintro ⟨⟨_, h⟩, hp⟩
    exact ⟨⟨Nat.zero_le _, h⟩, hp⟩

theorem thetaPow_nonneg (b y : ℝ) : 0 ≤ thetaPow b y :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `Π_a(x) = Σ_{k≥1} (1/k) θ_{ka}(x^{1/k})`, with the sum up to any `N ≥ log₂ x`. -/
theorem piA_eq_sum_layers (a : ℝ) {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    piA a x = ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) * thetaPow (k * a) (x ^ ((1 : ℝ) / k)) := by
  have h1 : piA a x = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow,
      ((n : ℝ) ^ a / log n * Λ n) := by
    unfold piA
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, Finset.sum_filter]
    simp only [ArithmeticFunction.map_zero, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, mul_zero]
  rw [h1, Chebyshev.sum_PrimePow_eq_sum_sum' _ hx hN]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  rw [thetaPow_eq_Ioc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hlp : log (p : ℝ) ≠ 0 := (log_pos hp1).ne'
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hpp]
  push_cast
  rw [log_pow, ← rpow_natCast, ← rpow_mul hp0]
  field_simp

theorem Icc_three_max (n : ℕ) : Finset.Icc 3 (max 2 n) = Finset.Icc 3 n := by
  ext k
  simp only [Finset.mem_Icc]
  omega

/-- **`Π_a(x) = θ_a(x) + ½ θ_{2a}(√x) + R(x)`**. -/
theorem piA_eq_layers (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    piA a x = thetaPow a x + (1 / 2) * thetaPow (2 * a) √x + layersR a x := by
  rw [piA_eq_sum_layers a hx (le_max_right 2 _)]
  have hset : Finset.Icc 1 (max 2 ⌊log x / log 2⌋₊) =
      {1, 2} ∪ Finset.Icc 3 (max 2 ⌊log x / log 2⌋₊) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd : Disjoint ({1, 2} : Finset ℕ) (Finset.Icc 3 (max 2 ⌊log x / log 2⌋₊)) := by
    rw [Finset.disjoint_left]
    intro k hk hk2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [Finset.mem_Icc] at hk2
    omega
  rw [hset, Finset.sum_union hd, Icc_three_max, Finset.sum_pair (by norm_num)]
  unfold layersR
  have h2 : x ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = √x := by
    rw [sqrt_eq_rpow]
    norm_num
  rw [h2]
  simp

/-- `Σ_{1≤n≤N} n^{−c} ≤ N^{1−c}/(1−c)`, for `0 ≤ c < 1`. -/
theorem sum_rpow_neg_le {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-c) ≤ (N : ℝ) ^ (1 - c) / (1 - c) := by
  have hr : 0 < 1 - c := by linarith
  induction N with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, Nat.cast_zero]
    rw [zero_rpow hr.ne', zero_div]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    set M : ℝ := ((N + 1 : ℕ) : ℝ) with hM
    have hNM : (N : ℝ) = M * (1 + (-(1 / M))) := by
      rw [hM]
      push_cast
      field_simp
      ring
    have hu : -1 ≤ -(1 / M) := by
      have : 1 / M ≤ 1 := by
        rw [div_le_one hN1, hM]
        push_cast
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith
      linarith
    have hB := rpow_one_add_le_one_add_mul_self hu hr.le (by linarith)
    have hstep : (N : ℝ) ^ (1 - c) ≤ M ^ (1 - c) - (1 - c) * M ^ (-c) := by
      have hsplit : (N : ℝ) ^ (1 - c) = M ^ (1 - c) * (1 + (-(1 / M))) ^ (1 - c) := by
        rw [hNM, mul_rpow hN1.le (by linarith)]
      have hMc : M ^ (1 - c) * (1 / M) = M ^ (-c) := by
        rw [sub_eq_add_neg, rpow_add hN1, rpow_one]
        field_simp
      rw [hsplit]
      have hpos : 0 < M ^ (1 - c) := by positivity
      calc M ^ (1 - c) * (1 + (-(1 / M))) ^ (1 - c)
          ≤ M ^ (1 - c) * (1 + (1 - c) * (-(1 / M))) := mul_le_mul_of_nonneg_left hB hpos.le
        _ = M ^ (1 - c) - (1 - c) * (M ^ (1 - c) * (1 / M)) := by ring
        _ = _ := by rw [hMc]
    have hgoal : (N : ℝ) ^ (1 - c) / (1 - c) + M ^ (-c) ≤ M ^ (1 - c) / (1 - c) := by
      rw [div_add' _ _ _ hr.ne', div_le_div_iff_of_pos_right hr]
      nlinarith
    linarith

/-- The uniform bound on the layer `k`, for `x ≥ 1`, `k ≥ 3`. -/
theorem thetaPow_layer_le {a δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη1 : a + 1 / 3 ≤ η)
    (hη2 : δ / 3 ≤ η) {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 3 ≤ k) :
    thetaPow (k * a) (x ^ ((1 : ℝ) / k)) ≤ x ^ η / δ := by
  have hx0 : 0 < x := by linarith
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set y := x ^ ((1 : ℝ) / k) with hy
  have hy1 : 1 ≤ y := one_le_rpow hx (by positivity)
  have hy0 : 0 < y := by linarith
  have hyk : y ^ (k : ℝ) = x := by
    rw [hy, ← rpow_mul hx0.le, one_div, inv_mul_cancel₀ hk0.ne', rpow_one]
  have hη0 : 0 ≤ η := by linarith [div_pos hδ0 (by norm_num : (0 : ℝ) < 3)]
  have hpow : ∀ e : ℝ, y ^ e = x ^ (e / k) := by
    intro e
    rw [hy, ← rpow_mul hx0.le]
    congr 1
    field_simp
  have hk1 : (1 : ℝ) / k ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  rcases le_or_gt 0 a with ha | ha
  · -- `a ≥ 0`
    have hterm : ∀ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ ((k : ℝ) * a) ≤ x ^ a := by
      intro p hp
      have hple : (p : ℝ) ≤ y := by
        have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
        exact (Nat.cast_le.mpr h).trans (Nat.floor_le hy0.le)
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      calc (p : ℝ) ^ ((k : ℝ) * a) ≤ y ^ ((k : ℝ) * a) :=
            rpow_le_rpow hp0 hple (by positivity)
        _ = x ^ a := by rw [rpow_mul hy0.le, hyk]
    have hcard : (((Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime).card : ℝ) ≤ y := by
      have h1 : ((Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime).card ≤ ⌊y⌋₊ := by
        refine (Finset.card_filter_le _ _).trans ?_
        simp
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hy0.le)
    rw [thetaPow_eq_Ioc]
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul] at hsum
    have hya : y * x ^ a ≤ x ^ η := by
      have h1 : y * x ^ a = x ^ ((1 : ℝ) / k + a) := by
        rw [rpow_add hx0]
      rw [h1]
      refine rpow_le_rpow_of_exponent_le hx ?_
      linarith
    have hxa : 0 ≤ x ^ a := by positivity
    have hd : x ^ η ≤ x ^ η / δ := by
      rw [le_div_iff₀ hδ0]
      have hxη : 0 ≤ x ^ η := by positivity
      nlinarith
    calc _ ≤ ((((Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime).card : ℝ)) * x ^ a := hsum
      _ ≤ y * x ^ a := mul_le_mul_of_nonneg_right hcard hxa
      _ ≤ x ^ η := hya
      _ ≤ _ := hd
  · -- `a < 0`
    set b : ℝ := -((k : ℝ) * a) with hb
    have hb0 : 0 < b := by
      rw [hb]
      nlinarith
    set b' : ℝ := min b (1 - δ) with hb'
    have hb'0 : 0 ≤ b' := le_min hb0.le (by linarith)
    have hb'1 : b' ≤ 1 - δ := min_le_right _ _
    have hb'b : b' ≤ b := min_le_left _ _
    have hb'lt : b' < 1 := by linarith
    have hr : 0 < 1 - b' := by linarith
    have hsub : thetaPow ((k : ℝ) * a) y ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℝ) ^ (-b') := by
      rw [thetaPow_eq_Ioc]
      calc ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ ((k : ℝ) * a)
          ≤ ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ (-b') := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hpp := (Finset.mem_filter.mp hp).2
            have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
            refine rpow_le_rpow_of_exponent_le hp1 ?_
            rw [hb] at hb'b
            linarith
        _ ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℝ) ^ (-b') := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
            intro p hp
            have h := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
            exact Finset.mem_Icc.mpr ⟨h.1, h.2⟩
    have hN : ((⌊y⌋₊ : ℕ) : ℝ) ^ (1 - b') ≤ y ^ (1 - b') :=
      rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hy0.le) hr.le
    have hexp : (1 - b') / k ≤ η := by
      rw [div_le_iff₀ hk0]
      rcases le_total b (1 - δ) with h | h
      · have : b' = b := min_eq_left h
        rw [this, hb]
        have h3 : 1 ≤ (k : ℝ) * (1 / 3) := by linarith
        nlinarith
      · have : b' = 1 - δ := min_eq_right h
        rw [this]
        have h3 : δ / 3 * k ≤ η * k := mul_le_mul_of_nonneg_right hη2 hk0.le
        nlinarith
    have hδr : δ ≤ 1 - b' := by linarith
    calc thetaPow ((k : ℝ) * a) y ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n : ℝ) ^ (-b') := hsub
      _ ≤ ((⌊y⌋₊ : ℕ) : ℝ) ^ (1 - b') / (1 - b') := sum_rpow_neg_le hb'0 hb'lt _
      _ ≤ y ^ (1 - b') / (1 - b') := div_le_div_of_nonneg_right hN hr.le
      _ ≤ y ^ (1 - b') / δ := div_le_div_of_nonneg_left (by positivity) hδ0 hδr
      _ = x ^ ((1 - b') / k) / δ := by rw [hpow]
      _ ≤ x ^ η / δ := div_le_div_of_nonneg_right (rpow_le_rpow_of_exponent_le hx hexp) hδ0.le

theorem layersR_nonneg (a x : ℝ) : 0 ≤ layersR a x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (thetaPow_nonneg _ _)

/-- **`0 ≤ R(x) ≤ C x^{a+½}/log² x`** for `x ≥ 3`. -/
theorem layersR_le {a : ℝ} (ha : -1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → layersR a x ≤ C * (x ^ (a + 1 / 2) / log x ^ 2) := by
  set κ := a + 1 / 2 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set δ := min (1 / 2) κ with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) hκ0
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδκ : δ ≤ κ := min_le_right _ _
  set η := max (a + 1 / 3) (δ / 3) with hη
  have hηκ : η < κ := max_lt (by rw [hκ]; linarith) (by linarith)
  obtain ⟨D, hD, hDb⟩ := log_pow_le_rpow 3 (sub_pos.mpr hηκ)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  refine ⟨1 / log 2 * (1 / δ) * D, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hterm : ∀ k ∈ Finset.Icc 3 ⌊log x / log 2⌋₊,
      (1 / (k : ℝ)) * thetaPow (k * a) (x ^ ((1 : ℝ) / k)) ≤ x ^ η / δ := by
    intro k hk
    have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk1 : (1 : ℝ) ≤ k := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    have h := thetaPow_layer_le (a := a) hδ0 hδ1 (le_max_left _ _) (le_max_right _ _) hx1 hk3
    have h0 := thetaPow_nonneg ((k : ℝ) * a) (x ^ ((1 : ℝ) / k))
    have hi : 1 / (k : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hk1
    calc (1 / (k : ℝ)) * thetaPow (k * a) (x ^ ((1 : ℝ) / k))
        ≤ 1 * thetaPow (k * a) (x ^ ((1 : ℝ) / k)) := mul_le_mul_of_nonneg_right hi h0
      _ ≤ x ^ η / δ := by rw [one_mul]; exact h
  have hcard : ((Finset.Icc 3 ⌊log x / log 2⌋₊).card : ℝ) ≤ log x / log 2 := by
    have h1 : (Finset.Icc 3 ⌊log x / log 2⌋₊).card ≤ ⌊log x / log 2⌋₊ := by
      rw [Nat.card_Icc]
      omega
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hxη : 0 ≤ x ^ η / δ := by positivity
  have h3 := hDb x hx1
  have hk : x ^ κ = x ^ η * x ^ (κ - η) := by
    rw [← rpow_add hx0]
    ring_nf
  have hfin : log x * x ^ η ≤ D * (x ^ κ / log x ^ 2) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity), hk]
    have hxp : 0 < x ^ η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hxp.le]
  unfold layersR
  calc _ ≤ ((Finset.Icc 3 ⌊log x / log 2⌋₊).card : ℝ) * (x ^ η / δ) := hsum
    _ ≤ log x / log 2 * (x ^ η / δ) := mul_le_mul_of_nonneg_right hcard hxη
    _ = 1 / log 2 * (1 / δ) * (log x * x ^ η) := by field_simp
    _ ≤ 1 / log 2 * (1 / δ) * (D * (x ^ κ / log x ^ 2)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = _ := by ring

/-- **Theorem 3, Step 3** (the layers `k ≥ 3`): for every real `a > −½`,
`Σ_{k≥3} (1/k) θ_{ka}(x^{1/k}) = o(x^{a+½}/log x)`. -/
theorem step3_layers {a : ℝ} (ha : -1 / 2 < a) :
    (fun x : ℝ => layersR a x) =o[atTop] (fun x : ℝ => x ^ (a + 1 / 2) / log x) := by
  obtain ⟨C, hC, hb⟩ := layersR_le ha
  rw [isLittleO_iff]
  intro ε hε
  have hlog : Tendsto log atTop atTop := tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog.eventually_ge_atTop ((C + 1) / ε)] with x hx hx2
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hxk : 0 < x ^ (a + 1 / 2) / log x := by positivity
  rw [Real.norm_of_nonneg (layersR_nonneg a x), Real.norm_of_nonneg hxk.le]
  refine (hb x hx).trans ?_
  have hid : x ^ (a + 1 / 2) / log x ^ 2 = x ^ (a + 1 / 2) / log x * (1 / log x) := by
    field_simp
  rw [hid, mul_comm, mul_assoc]
  rw [mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ hxk.le
  rw [show 1 / log x * C = C / log x by ring, div_le_iff₀ hl]
  have h1 : (C + 1) / ε * ε = C + 1 := by field_simp
  have : (C + 1) / ε * ε ≤ log x * ε := mul_le_mul_of_nonneg_right hx2 hε.le
  linarith

end CpsLean
