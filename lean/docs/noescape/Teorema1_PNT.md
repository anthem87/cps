# Blocco B, parte PNT: conseguenze del PNT, Teorema 1, Teorema 2 (asintotica), Proposizione 2, Corollario 2

λ = FOL classica + analisi reale di Mathlib (limiti, `IsEquivalent`, `IsBigO`, integrale di Lebesgue su
intervalli, sommazione di Abel). Ordine (audit §2): conseguenze del PNT → Teor. 1(i) → [Teor. 2
elementare, già nel Blocco A] → Teor. 1(ii) → Teor. 2 (asintotica), Prop. 2, Cor. 2.

## Γ₀
- **PNT** (ipotesi classica, `def PNT : Prop`; Hadamard, de la Vallée Poussin 1896):
  `π(x) ∼ x/log x` per `x → ∞` (`x` reale, `π(x) = π(⌊x⌋)`).
- M1 sommazione di Abel (Mathlib `sum_mul_eq_sub_integral_mul`):
  `Σ_{k≤x} f(k) c_k = f(x) Σ_{k≤x} c_k − ∫_0^x f′(t) Σ_{k≤t} c_k dt`.
- M2 teorema fondamentale del calcolo (`intervalIntegral.integral_eq_sub_of_hasDerivAt`), monotonia
  dell'integrale, `IsEquivalent` (prodotti, quozienti, composizione con funzioni che tendono a ∞).
- M3 Blocco A: Teor. 2 (`σ_{m(t)−1} < t ≤ σ_{m(t)}`, `p_{m(t)} = N(t)`), Def. 1, lean-base
  (`PNTcons`, `r_asymp`: `PNTcons ⇒ m·Δ_m → 2` in indici lean-base).

## Lemmi intermedi (tutti foglie dimostrate, nessuna ipotesi nuova)
- **G (integrale di equivalenti).** `f ∼ g`, `g ≥ 0`, `∫_2^x g → ∞` ⇒ `∫_2^x f ∼ ∫_2^x g`.
  Prova: per ogni `η > 0`, `|f − g| ≤ η g` su `[T, ∞)`; `|∫_2^x (f − g)| ≤ C_T + η ∫_2^x g`.
- **H.** `∫_2^x t dt/log t ∼ x²/(2 log x)`. Prova: `F(t) = t²/(2 log t)` ha
  `F′(t) = t/log t − t/(2 log² t)` (M2), quindi `∫_2^x t/log t = F(x) − F(2) + ½∫_2^x t/log² t`;
  spezzando in `√x`: `∫_2^x t/log² t ≤ x/log² 2 + 4x²/(2 log² x) = o(x²/log x)`.
- **L1.** PNT ⇒ `Σ_{p≤x} p ∼ x²/(2 log x)`. Prova: M1 con `f(t) = t`, `c = 1_P`:
  `Σ_{p≤x} p = x π(x) − ∫_0^x π(t) dt`; `x π(x) ∼ x²/log x` (PNT); `∫_2^x π(t) dt ∼ ∫_2^x t/log t`
  (G, PNT) `∼ x²/(2 log x)` (H); la differenza: `x²/log x · (1 + o(1)) − x²/(2 log x) · (1 + o(1))`.
- **L2.** PNT ⇒ `p_{m+1}/p_m → 1`. Prova: per `η > 0`, `π((1+η)x)/π(x) → 1 + η > 1` (PNT, e
  `log((1+η)x)/log x → 1`), quindi c'è un primo in `(x, (1+η)x]` per `x` grande; con `x = p_m → ∞`,
  `p_{m+1} ≤ (1+η) p_m`.
- **L3.** PNT ⇒ `PNTcons` di lean-base: L2 e `S_{p_m}/(m p_m) → 1/2` da L1 (`S_{p_m} ∼ p_m²/(2 log p_m)`)
  e PNT (`π(p_m) = m ∼ p_m/log p_m`); l'indice di lean-base è spostato di 1, che non cambia i limiti.

## Albero
```
 1. PNT ⊢ PNTcons                                        [L3]
 2. PNT ⊢ m·Δ_m → 2, cioè Δ_m ∼ 2/m           — Teor. 1(i) [1, r_asymp (lean-base), ponte degli indici]
 3. PNT ⊢ m(t) → ∞ per t → ∞                              [M3: t > σ_M ⇒ m(t) > M]
 4. PNT ⊢ ε(t) → 0, δ(t) → 0                              [2, 3, Teor. 2(d): ε < δ = Δ_{m(t)−1}]
 5. PNT ⊢ log S(N(t)) − t → 0                             [4: è ε(t)]
 6. PNT ⊢ log S(N) = 2 log N − log log N − log 2 + o(1)   [L1 lungo N → ∞; S(N) = 1 + Σ_{p≤N} p]
 7. PNT ⊢ t = 2 log N(t) − log log N(t) − log 2 + o(1)    — Prop. 2 [5, 6, N(t) → ∞]
 8. PNT ⊢ log N(t) ∼ t/2                                  [7: log log N = o(log N)]
 9. PNT ⊢ N(t) ∼ √(2 log N(t)) e^{t/2} ∼ √t e^{t/2}       — Cor. 2, prima parte [7, 8]
10. PNT ⊢ N(t′)/N(t) = e^{(t′−t)/2}√(t′/t)(1 + o(1)), o(1) per t → ∞ uniforme in t′ ≥ t
                                                          — Cor. 2 [9: rapporto di due quantità in (1−η, 1+η)]
11. PNT ⊢ δ(t) ∼ 2/m(t) ∼ 2 log N(t)/N(t)                 [2, 3; m(t) = π(N(t)) ∼ N/log N (PNT)]
12. PNT ⊢ δ(t) ∼ √t e^{−t/2}                 — Teor. 1(ii) e Teor. 2 (asintotica) [11, 8, 9]
```

## Audit
- R7: l'unica ipotesi classica è PNT; le altre foglie sono Mathlib, lean-base o lemmi intermedi
  G, H, L1–L3 dimostrati qui.
- R8: nessun buco. R9: t, t′, m, η autovariabili; le soglie `T` sono testimoni di ∃E scaricati.
- R10: FOL classica + analisi di Mathlib; solo assiomi standard.
- Quantificatori (A11): nel Cor. 2, `o(1)` per `t → ∞`, uniforme in `t′ ≥ t`.

**Verdetto: CHIUSA**, Γ₀ = {PNT, M1, M2, M3}.
