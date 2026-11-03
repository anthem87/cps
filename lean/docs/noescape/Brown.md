# Osservazione dopo il Teorema 2 (criterio di Brown)

λ = FOL classica su ℕ e sui sottoinsiemi finiti di ℕ.

Enunciato del paper: per `1, 2, 3, 5, …` il criterio di Brown si legge `p_{m+1} ≤ S_{p_m} + 1`; la
condizione `S_{p_m} ≥ p_{m+1}` del Teorema 2 lo implica, e ogni intero tra `1` e `S_{p_m}` è somma di
elementi distinti di `{1, 2, 3, 5, …, p_m}`.

## Dizionario
`W_m = {1} ∪ {q primo : q ≤ p_m}` (Finset di ℕ; `1` non è primo, quindi l'unione è disgiunta);
`Σ W_m = S(p_m)`.

Goal: `∀ m ≥ 1`, (i) `p_{m+1} ≤ S(p_m) + 1`; (ii) `∀ T, 1 ≤ T ≤ S(p_m) → ∃ A ⊆ W_m, Σ_{a∈A} a = T`.

## Γ₀
- H1 Teorema 2(a): `p_{m+1} ≤ S(p_m)`.
- H2 `W_{m+1} = W_m ∪ {p_{m+1}}`, `p_{m+1} ∉ W_m` (non ci sono primi tra `p_m` e `p_{m+1}`;
  `p_{m+1} > p_m ≥ 2 > 1`), quindi `Σ W_{m+1} = Σ W_m + p_{m+1}`.
- H3 `W_1 = {1, 2}`, `S(p₁) = 3`.

## Albero (si dimostra (ii) per ogni `T ≤ S(p_m)`, includendo `T = 0` con `A = ∅`)
```
 1. (i): p_{m+1} ≤ S(p_m) ≤ S(p_m) + 1                    [H1]
 2. base m = 1: T ∈ {0,1,2,3}: A = ∅, {1}, {2}, {1,2}     [H3, casi]
 3. passo: IH per m; T ≤ S(p_{m+1}) = S(p_m) + p_{m+1}    [H2]
 4.   caso T ≤ S(p_m): A dall'IH, A ⊆ W_m ⊆ W_{m+1}        [∨E]
 5.   caso T > S(p_m): T ≥ p_{m+1}                         [H1: S(p_m) ≥ p_{m+1}]
 6.     T − p_{m+1} ≤ S(p_m); A' dall'IH per T − p_{m+1}   [3, 5]
 7.     A := A' ∪ {p_{m+1}}, p_{m+1} ∉ A' ⊆ W_m            [H2]
 8.     Σ A = (T − p_{m+1}) + p_{m+1} = T                  [Finset.sum_insert]
```

## Audit
- R7: foglie H1–H3, aritmetica di ℕ. R8: nessun buco. R9: T, m autovariabili; A, A' testimoni scaricati.
- R10: FOL classica + induzione su m. Il lemma di Brown generale di lean-base (`brown_mpr`) non serve:
  l'induzione sopra è la sua prova, specializzata.

**Verdetto: CHIUSA in FOL classica**, Γ₀ = {H1, H2, H3}.
