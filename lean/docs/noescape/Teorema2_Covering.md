# Teorema 2 (Covering), parte elementare

λ = FOL classica a due sorte (ℕ, ℝ). Base: §1 dell'audit del 3 novembre 2026, verificato contro il tex,
con l'aggiunta di `ε(log 3) = 0` (A2) e la nota N1 (G5) di DIVERGENZE.md.

## Dizionario
Come in `Prop1_Def12.md`; inoltre `Δ_m = σ_{m+1} − σ_m`, `m(t) = π(N(t))` (l'indice del primo
d'attraversamento: `p_{m(t)} = N(t)`), `δ(t) = σ_{m(t)} − σ_{m(t)−1}`.

Goal:
- (a) `∀ m ≥ 1, p_{m+1} ≤ S(p_m)`;
- (b) `∀ m ≥ 1, Δ_m ≤ log 2 ∧ (Δ_m = log 2 ↔ m = 1)`;
- (c) `ε(log 3) = 0`;
- (d) `∀ t > log 3, 0 ≤ ε(t) ∧ ε(t) < δ(t) ∧ δ(t) ≤ log 2`.

## Γ₀
- H1 Bertrand (Mathlib `Nat.exists_prime_lt_and_le_two_mul`): `∀ n ≠ 0 ∃ q primo, n < q ≤ 2n`.
- H2 `∀ n ≥ 2, 2n` non è primo (`Nat.not_prime_mul`).
- H3 successore: `∀ m ∀ q primo, q > p_m → q ≥ p_{m+1}` (`Nat.le_nth_of_lt_nth_succ`).
- H4 passo della somma: `S(p_{m+1}) = S(p_m) + p_{m+1}` (lean-base `S_succ`, tramite il ponte degli indici).
- H5 `p₁ = 2`, `p₂ = 3`, `S(p₁) = 3`; `p_m ≥ 2`.
- H6 Prop. 1 e le proprietà di `N(t)` (`Prop1_Def12.md`): per `t ≥ log 3`, `N(t)` primo,
  `t ≤ log S(N(t))`, e nessun primo `q < N(t)` ha `t ≤ log S q`.
- H7 `log` crescente; `log(1+u) ≤ log 2 ⟺ u ≤ 1`, con `=` sse `u = 1` (u ≥ 0).
- H8 `π(p_m) = m` e `p_{π(q)} = q` per q primo (`Nat.nth_count`, `Nat.primeCounting`).

## Albero
```
 1. S(p₁) = 3 = p₂                                       [H5]
 2. ∀ m ≥ 1: S(p_m) ≥ p_{m+1}  (a)                        [induzione: base 1; passo: IH S(p_m) ≥ p_{m+1} ⇒ S(p_{m+1}) = S(p_m) + p_{m+1} ≥ 2p_{m+1} (H4) > p_{m+2} (H1 con n = p_{m+1}, H2, H3)]
 3. ∀ m ≥ 2: S(p_m) > p_{m+1}                            [dal passo di 2: per m = k+1 ≥ 2, S(p_{k+1}) ≥ 2p_{k+1} > p_{k+2}]
 4. Δ_m = log(1 + p_{m+1}/S(p_m))                         [H4, log_div]
 5. Δ_m ≤ log 2, con = sse p_{m+1} = S(p_m)               [H7, (a)]
 6. p_{m+1} = S(p_m) ⟺ m = 1                              [1; 3]                       — (b)
 7. ε(log 3) = log S(N(log 3)) − log 3 = 0                [N(log 3) = 2: 2 primo, log S 2 = log 3, nessun primo < 2] — (c)
 8. [t > log 3]  m := m(t), N(t) = p_m                    [H6, H8]
 9. m ≥ 2                                                 [N(t) ≠ 2: log S 2 = log 3 < t]
10. σ_{m−1} < t ≤ σ_m                                     [t ≤ log S(p_m) (H6); p_{m−1} < N(t) primo ⇒ ¬(t ≤ σ_{m−1}) (H6)]
11. ε(t) = σ_m − t ≥ 0                                    [10]
12. ε(t) < σ_m − σ_{m−1} = δ(t)                           [10]
13. δ(t) = Δ_{m−1} ≤ log 2                                [5, m − 1 ≥ 1]                — (d)
```
La riga 2 è l'induzione del paper: `S(p_m) = S(p_{m−1}) + p_m ≥ 2p_m > p_{m+1}`.

## Audit
- R7 foglie: H1–H8 (Mathlib, lean-base, definizioni, Prop. 1); aritmetica.
- R8: nessun buco. La disuguaglianza stretta di 2 usa H2 (nota N1: non è un difetto del paper).
- R9: m, t autovariabili di ∀I; q testimone di Bertrand scaricato in 2.
- R10: FOL classica, induzione su ℕ; in Lean solo gli assiomi standard.

**Verdetto: CHIUSA in FOL classica**, Γ₀ = {H1, …, H8}. La parte asintotica del Teorema 2 è il
Teorema 1(ii) (nota N5), fuori da questo blocco.
