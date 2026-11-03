# Definizioni 1–2 e Proposizione 1

λ = FOL classica a due sorte (ℕ, ℝ). Classica perché `min` di un insieme non vuoto di ℕ si prende con
il buon ordinamento (in Lean: `sInf`, `Nat.sInf_mem`, `Nat.sInf_le`), e l'esistenza di un elemento
oltre ogni soglia si ottiene per assurdo dall'illimitatezza.

## Dizionario
- `p_m` = `Nat.nth Nat.Prime (m − 1)` (m ≥ 1; `p₁ = 2`).
- `S N` = `1 + Σ_{q ≤ N, q primo} q` (in ℕ); `σ_m = log S(p_m)` (in ℝ).
- `N(t)` = `sInf {p | p primo ∧ t ≤ log S p}`; `ε(t) = log S(N(t)) − t`.
- `M(t)` = `sInf {N | 1 ≤ N ∧ t ≤ log S N}` (il minimo su tutti gli N della prova del paper).

Goal (Def. 1): `σ` strettamente crescente su m ≥ 1 e `σ₁ = log 3`.
Goal (Prop. 1, forma D1): `∀ t ≥ log 3, M(t) = N(t) ∧ N(t) primo`.

## Γ₀
- H1 `Nat.nth_strictMono`, `Nat.nth_prime_zero_eq_two`, `Nat.nth_prime_one_eq_three` (Mathlib).
- H2 `S` è monotona in N, e `S(N+1) = S N + (N+1)` se `N+1` è primo, `S(N+1) = S N` altrimenti
  (definizione di `S`, `Finset.range_add_one`, `filter_insert`).
- H3 `S N ≥ N` per ogni N ≥ 1 (da H2 per induzione: ogni passo aggiunge 0 o N+1 ≥ 1; `S 1 = 1`).
- H4 infinità dei primi: `∀ n ∃ p primo, n ≤ p` (`Nat.exists_infinite_primes`).
- H5 `log` strettamente crescente su (0, ∞) (`Real.log_lt_log`).

## Albero
```
Def. 1
 1. S(p_{m+1}) = S(p_m) + p_{m+1} > S(p_m)            [H2 iterata: tra p_m e p_{m+1} non ci sono primi (Nat.le_nth_of_lt_nth_succ)]
 2. σ_{m+1} > σ_m                                      [H5, 1; S(p_m) ≥ 1 > 0]
 3. σ₁ = log S 2 = log 3                               [H1: p₁ = 2; S 2 = 1 + 2]
Prop. 1 (fisso t ≥ log 3; ∀I, t non libera in Γ₀)
 4. A := {N | 1 ≤ N ∧ t ≤ log S N} ≠ ∅                 [H3, H4, H5: scelgo N ≥ max(1, e^t) primo; log S N ≥ log N ≥ t]
 5. P := {p | p primo ∧ t ≤ log S p} ≠ ∅               [come 4, con il primo di H4]
 6. M := M(t) ∈ A, ∀N ∈ A, M ≤ N                       [Nat.sInf_mem 4, Nat.sInf_le]
 7. M ≥ 2                                              [M = 1 ⇒ log S 1 = log 1 = 0 ≥ t ≥ log 3 > 0: assurdo (RAA)]
 8. M primo                                            [RAA: se M non primo, M ≥ 2 ⇒ M − 1 ≥ 1 e S(M−1) = S M (H2), quindi M−1 ∈ A, contro 6]
 9. M ∈ P, quindi N(t) ≤ M                             [6, 8; Nat.sInf_le]
10. N(t) ∈ P ⊆ A, quindi M ≤ N(t)                      [Nat.sInf_mem 5; un primo è ≥ 1; 6]
11. M = N(t) ∧ N(t) primo                              [9, 10, antisimmetria; 8]
```

## Audit
- R7 foglie: H1–H5 (Mathlib o definizione), aritmetica di ℕ e ℝ; nessuna foglia fuori da Γ₀.
- R8 nessun buco ("chiaramente", omissis): assenti.
- R9 variabili: t introdotta da ∀I (condizione: non libera in Γ₀ ✓); N, p testimoni di ∃E (H4) scaricati in 4–5.
- R10 dipendenze: regole FOL + RAA (passi 7, 8, marcati), buon ordinamento di ℕ; in Lean
  propext, Classical.choice, Quot.sound.

**Verdetto: CHIUSA in FOL classica**, Γ₀ = {H1, …, H5}. Ipotesi non usate: nessuna.
