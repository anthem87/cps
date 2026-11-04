# Blocco C, punto 3a: Teorema 3, Step 3 (i layer k ≥ 3), con la correzione G2

λ = FOL classica + analisi reale di Mathlib. Nessuna ipotesi classica: è incondizionato.

## Γ₀
- M1 Mathlib `Chebyshev.sum_PrimePow_eq_sum_sum'`: somma sulle potenze di primi = somma doppia.
- M2 Bernoulli `(1 + s)^r ≤ 1 + rs` per `s ≥ −1`, `0 ≤ r ≤ 1`.

## Goal
`R(x) = Σ_{k≥3} (1/k) θ_{ka}(x^{1/k}) = o(x^{a+½}/log x)`, e la forma che serve allo Step 4:
`0 ≤ R(x) ≤ C x^{a+½}/log²x` per `x ≥ 3`.

## Albero
```
 1. ⊢ Π_a(x) = θ_a(x) + ½ θ_{2a}(√x) + R(x), per x ≥ 2         [M1; Λ(p^k)/log(p^k) = 1/k]
 2. M2 ⊢ Σ_{1≤n≤N} n^{−c} ≤ N^{1−c}/(1−c), 0 ≤ c < 1            [induzione: N^r ≤ (N+1)^r − r (N+1)^{r−1}, r = 1−c]
 3. Sia κ = a + ½, δ = min(½, κ), η = max(a + ⅓, δ/3): η < κ.
 4. a ≥ 0, k ≥ 3, x ≥ 1 ⊢ θ_{ka}(x^{1/k}) ≤ x^{1/k} x^a ≤ x^η             [p^{ka} ≤ x^a; numero di primi ≤ x^{1/k}]
 5. a < 0, k ≥ 3, x ≥ 1 ⊢ θ_{ka}(x^{1/k}) ≤ x^η/δ:
      con b = k|a|, b′ = min(b, 1−δ): n^{−b} ≤ n^{−b′}; 2 con c = b′; 1 − b′ ≥ δ;
      (1−b′)/k ≤ η   [se b′ = b: 1/k − |a| = 1/k + a ≤ a + ⅓; se b′ = 1−δ: δ/k ≤ δ/3]
 6. ⊢ 0 ≤ R(x) ≤ (log x/log 2) x^η/(3δ)          [k ≤ log x/log 2 termini, 1/k ≤ ⅓; 4, 5]
 7. ⊢ R(x) ≤ C x^κ/log²x                        [log³x ≪ x^{κ−η}]
 8. ⊢ R = o(x^κ/log x)                          [7; 1/log x → 0]
```

## G2
Il paper separa i `k` con `ka > −1`, `ka < −1` e i valori di transizione `ka ≈ −1`; G2 corregge questi ultimi
(O(1) valori di `k`, ciascuno `≪ x^{a+⅓} log log x`). La prova qui non li separa: l'esponente uniforme `b′`
del passo 5 copre tutti i `k`, senza logaritmi di transizione. La conclusione del paper resta la stessa.

## Audit
- R7: foglie M1, M2. R8: nessun buco. R9: `x, k, n` autovariabili. R10: FOL classica.

**Verdetto: CHIUSA**, Γ₀ = {M1, M2}.
