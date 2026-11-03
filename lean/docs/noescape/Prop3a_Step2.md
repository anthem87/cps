# Blocco B, parte RH: Proposizione 3(a) e Teorema 3, Step 2

λ = FOL classica + analisi reale di Mathlib. RH entra solo come antecedente.

## Γ₀
- **VonKochPsi** (ipotesi classica, `def VonKochPsi : Prop`; von Koch 1901, Davenport cap. 18):
  `RiemannHypothesis → ψ(x) − x = O(√x log² x)`.
- M1 Mathlib `Chebyshev.isBigO_psi_sub_theta_sqrt`: `ψ − θ = O(√x)`.
- M2 sommazione di Abel (Mathlib) con pesi `c_n = log n · 1_P(n)`: per `f` derivabile su `[2, y]`,
  `Σ_{p≤y} f(p) log p = f(y) θ(y) − ∫_2^y f′(t) θ(t) dt`.
- M3 teorema fondamentale del calcolo, stime di integrali di potenze e logaritmi.
- M4 Blocco A: `S(N) − B(N) = Σ_{p≤N} p − ∫_2^N t/log t` (`S_sub_B_eq`), `B(x) = 1 + ∫_2^x t/log t`.

## Lemma W (somma pesata dei primi)
Identità (Abel, M2, con `f(t) = t^b/log t`, `θ = t + E`, `y ≥ 2`):
`Σ_{p≤y} p^b = ∫_2^y f + 2 f(2) + f(y)E(y) − ∫_2^y f′E` (il termine `t` dà `∫_2^y f + 2 f(2)` per FTC su
`t f(t)`). Due stime:
- `b = 1` (Prop. 3(a)): `|E(t)| ≤ C √t log² t` su `[2, ∞)`; `|f′(t)| ≤ (1 + 1/log 2)/log t`; quindi
  `|f(x)E(x)| + |∫_2^x f′E| ≤ C′ x^{3/2} log x`.
- `b > −1` (Step 2): con `γ = max(3/4, (1−b)/2)`, `½ < γ < 1`, `b + γ > 0`: `|E(t)| ≤ C t^γ` su `[2, ∞)`
  (perché `√t log² t = O(t^γ)`); `|f′(t)| ≤ K t^{b−1}`; quindi
  `|Σ_{p≤y} p^b − ∫_2^y f| ≤ A y^{b+γ}`, con `∫_2^y t^{b−1+γ} = (y^{b+γ} − 2^{b+γ})/(b+γ)`.
Le stime `O` a `+∞` diventano stime su `[2, ∞)` perché `θ(t) − t` è limitata sui compatti
(`|θ(t) − t| ≤ (log 4 + 1) t`, Chebyshev, Mathlib).

## Albero
```
 1. VonKochPsi, RH ⊢ ψ(x) − x = O(√x log² x)                    [→E]
 2. VonKochPsi, RH ⊢ θ(x) − x = O(√x log² x)                    [1, M1: √x = O(√x log² x)]
 3. VonKochPsi, RH ⊢ Σ_{p≤x} p = ∫_2^x t/log t + O(x^{3/2} log x)        [W con b = 1]
 4. VonKochPsi, RH ⊢ S(x) − B(x) = O(x^{3/2} log x)      — Prop. 3(a), prima parte [3, M4]
 5. ⊢ B(x) ≥ x²/(4 log x) per x ≥ 4; quindi S(x) ≥ x²/(8 log x) per x grande   [M3; 4]
 6. VonKochPsi, RH ⊢ |log S(x) − log B(x)| = O(log² x/√x)  — Prop. 3(a), seconda parte
                                                  [|log a − log b| ≤ |a − b|/min(a, b); 4, 5]
 7. ⊢ ∫_2^y t^b/log t = y^{b+1}/((b+1) log y)·(1 + O(1/log y))  (b > −1)
                                                  [FTC con F = t^{b+1}/((b+1) log t); ∫ t^b/log² t = O(y^{b+1}/log² y)]
 8. VonKochPsi, RH ⊢ θ_b(y) := Σ_{p≤y} p^b = y^{b+1}/((b+1) log y)·(1 + O(1/log y))   [W, 7: y^{b+γ} = o(y^{b+1}/log² y) perché γ < 1]
 9. VonKochPsi, RH ⊢ ½ θ_{2a}(√x) = x^{a+1/2}/((2a+1) log x)·(1 + O(1/log x)),  a > −½
                                                  — Teor. 3, Step 2 (riquadro) [8 con b = 2a, y = √x; log √x = ½ log x]
```

## Audit
- R7: l'unica ipotesi classica è VonKochPsi (con RH come antecedente); D3 di DIVERGENZE.md: l'errore
  `O(1/log x)` del riquadro viene da qui, non dal solo PNT.
- R8: nessun buco. R9: x, y, a, b autovariabili. R10: FOL classica + analisi di Mathlib.

**Verdetto: CHIUSA**, Γ₀ = {VonKochPsi, M1, M2, M3, M4}, RH come antecedente.
