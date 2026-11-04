module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.ZMod.Basic
set_option autoImplicit false

/-!
# Lucas certificates of primality

`powMod m f b e` is `b^e mod m` by repeated squaring, for `e < 2^f`; the kernel evaluates it with its
arithmetic on natural numbers. `prime_of_lucas` is Lucas' criterion (Mathlib's `lucas_primality`) with
the checks on `powMod`.
-/

open Nat

@[expose] public section

namespace CpsLean

/-- `b^e mod m`, by repeated squaring, with fuel `f`. -/
def powMod (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then powMod m f (b * b % m) (e / 2) * b % m
    else powMod m f (b * b % m) (e / 2)

theorem powMod_cast (m : ℕ) : ∀ (f b e : ℕ), e < 2 ^ f →
    ((powMod m f b e : ℕ) : ZMod m) = (b : ZMod m) ^ e := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp [powMod]
  | succ f ih =>
    intro b e he
    have hdiv : e / 2 < 2 ^ f := by
      rw [pow_succ] at he
      omega
    have hrec := ih (b * b % m) (e / 2) hdiv
    have hb : ((b * b % m : ℕ) : ZMod m) = (b : ZMod m) * b := by
      rw [ZMod.natCast_mod]
      push_cast
      ring
    rw [hb] at hrec
    unfold powMod
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [ZMod.natCast_mod]
      push_cast
      rw [hrec]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by omega, pow_succ, pow_mul]
      rw [sq]
    · rw [hrec]
      conv_rhs => rw [show e = 2 * (e / 2) by omega, pow_mul]
      rw [sq]

theorem powMod_lt {m : ℕ} (hm : 0 < m) : ∀ (f b e : ℕ), powMod m f b e < m := by
  intro f
  induction f with
  | zero => exact fun _ _ => Nat.mod_lt _ hm
  | succ f ih =>
    intro b e
    unfold powMod
    split_ifs
    · exact Nat.mod_lt _ hm
    · exact Nat.mod_lt _ hm
    · exact ih _ _

/-- **Lucas' criterion**, with the checks on `powMod`. `fs` is the list of the prime factors of `p − 1`,
with multiplicity. -/
theorem prime_of_lucas (p a : ℕ) (fs : List ℕ) (hp : 1 < p) (hfs : ∀ q ∈ fs, q.Prime)
    (hprod : fs.prod = p - 1) (hsmall : p - 1 < 2 ^ 64) (h1 : powMod p 64 a (p - 1) = 1)
    (h2 : ∀ q ∈ fs, powMod p 64 a ((p - 1) / q) ≠ 1) : p.Prime := by
  refine lucas_primality p (a : ZMod p) ?_ fun q hq hdvd => ?_
  · have := powMod_cast p 64 a (p - 1) hsmall
    rw [h1] at this
    rw [← this]
    simp
  · intro hone
    rw [← hprod] at hdvd
    obtain ⟨x, hx, hqx⟩ := (Nat.Prime.prime hq).dvd_prod_iff.mp hdvd
    have hxp := hfs x hx
    have hqe : q = x := (Nat.prime_dvd_prime_iff_eq hq hxp).mp hqx
    subst hqe
    have hcast := powMod_cast p 64 a ((p - 1) / q) (lt_of_le_of_lt (Nat.div_le_self _ _) hsmall)
    rw [hone] at hcast
    have hc : ((powMod p 64 a ((p - 1) / q) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [hcast]
      simp
    rw [ZMod.natCast_eq_natCast_iff'] at hc
    rw [Nat.mod_eq_of_lt (powMod_lt (by omega) _ _ _), Nat.mod_eq_of_lt hp] at hc
    exact h2 q hx hc

/-! ### Primality and sums of primes, by trial division -/

/-- Trial division by `d, d + 1, …`, with fuel `f`. -/
def trialOk (n : ℕ) : ℕ → ℕ → Bool
  | 0, d => decide (n < d * d)
  | f + 1, d =>
    if n < d * d then true else if n % d = 0 then false else trialOk n f (d + 1)

theorem trialOk_iff (n : ℕ) : ∀ (f d : ℕ), n < (d + f) * (d + f) →
    (trialOk n f d = true ↔ ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n) := by
  intro f
  induction f with
  | zero =>
    intro d hd
    simp only [add_zero] at hd
    simp only [trialOk, decide_eq_true_eq, hd, true_iff]
    intro m hm hmn
    have := Nat.mul_le_mul hm hm
    omega
  | succ f ih =>
    intro d hd
    unfold trialOk
    split_ifs with h1 h2
    · simp only [true_iff]
      intro m hm hmn
      have := Nat.mul_le_mul hm hm
      omega
    · simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨d, le_rfl, by omega, by simpa using Nat.dvd_of_mod_eq_zero h2⟩
    · rw [ih (d + 1) (by rw [show d + 1 + f = d + (f + 1) by ring]; exact hd)]
      constructor
      · intro h m hm hmn
        rcases eq_or_lt_of_le hm with rfl | hlt
        · exact fun hdvd => h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact h m hlt hmn
      · exact fun h m hm hmn => h m (by omega) hmn

/-- Primality, by trial division. -/
def primeB (n : ℕ) : Bool := decide (2 ≤ n) && trialOk n n 2

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq]
  rw [trialOk_iff n n 2 (by nlinarith)]
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hs => h m hm (Nat.le_sqrt.mp hs)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hs => h m hm (Nat.le_sqrt.mpr hs)⟩

/-- `acc + Σ_{k ≤ q < k + f, q prime} q`. -/
def sumLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | f + 1, k, acc => sumLoop f (k + 1) (if primeB k then acc + k else acc)

theorem sumLoop_eq : ∀ (f k acc : ℕ), sumLoop f k acc =
    acc + ∑ q ∈ Finset.Ico k (k + f), if q.Prime then q else 0 := by
  intro f
  induction f with
  | zero => simp [sumLoop]
  | succ f ih =>
    intro k acc
    have hIco : ∑ q ∈ Finset.Ico k (k + (f + 1)), (if q.Prime then q else 0) =
        (if k.Prime then k else 0) + ∑ q ∈ Finset.Ico (k + 1) (k + 1 + f), if q.Prime then q else 0 := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      congr 2
      ring
    rw [sumLoop, ih, hIco]
    by_cases hk : k.Prime
    · have : primeB k = true := (primeB_iff k).mpr hk
      simp only [this, if_true, hk, if_true]
      ring
    · have : primeB k = false := Bool.eq_false_iff.mpr fun h => hk ((primeB_iff k).mp h)
      simp only [this, Bool.false_eq_true, if_false, hk]
      ring

end CpsLean
