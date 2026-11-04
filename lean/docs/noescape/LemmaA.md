# Blocco C, punto 2: Lemma A, con la riparazione D2

λ = FOL classica + analisi di Mathlib. RH entra come ipotesi del teorema.

## Γ₀
- H1 `TruncatedExplicitFormula`, usata solo per `t ≥ 5/2 ≥ 2` e `T ≥ 2` (D2; G3 aperto sul volume).
- H2 `RiemannVonMangoldt`, tramite C1: `Σ_{ρ∈s} m(ρ)/|ρ+b|² ≤ K_b` per ogni finito `s` di zeri, e
  `Σ_{k<|γ|≤k+1} m(ρ) ≤ C√k` per `k ≥ K₀`.
- H3 `RiemannHypothesis`: `Re ρ = ½`, quindi `Re(ρ + a) = κ := a + ½ > 0`, `ρ ≠ 0`, `ρ + a ≠ 0`.
- M1 Abel (Mathlib, `sum_mul_eq_sub_sub_integral_mul`), FTC, stime di integrali, `Λ(n) ≤ log n`.
- M2 `li`: `∫_c^x t^a/log t = li(x^{a+1}) − li(c^{a+1})`, per `1 < c ≤ x`, `a > −1` (`LogIntPV`).

## Notazione
`v = 5/2`, `v₀ = log v`, `T = e^Y`, `f(t) = t^a/log t`, `s = ρ + a`, `S = {ρ : |γ| < T}` con molteplicità `m`,
`Z(t) = Σ_S m t^ρ/ρ`, `G(t) = ψ(t) − t + Z(t)`, `W_s(x) = ∫_v^x t^{s−1}/log³t`.

## Albero
```
 1. ⊢ Π_a(x) = 2^a + f(x)ψ(x) − f(v) log 2 − ∫_v^x f′ψ          [M1 con a := v; n = 2 dà 2^a; ψ(v) = log 2]
 2. H1 ⊢ ‖G(t)‖ ≤ C_G (t log²(tT)/T + log t + 1)   per t ≥ v, T ≥ 2
        [H1; min(1, ·) ≤ 1; |ζ′(0)/ζ(0)| e ½|log(1 − t⁻²)| costanti; |ψ − ψ₀| ≤ ½ log t]
 3. ⊢ ∫_v^x f′(t) t = x f(x) − v f(v) − ∫_v^x f                  [FTC su t f(t)]
 4. H3 ⊢ ∫_v^x f′ t^ρ/ρ = f(x)x^ρ/ρ − f(v)v^ρ/ρ − ∫_v^x t^{s−1}/log t   [FTC su f(t) t^ρ/ρ]
 5. 1, 3, 4, ψ = t − Z + G ⊢
    Π_a(x) = 2^a + ∫_v^x f − f(v)G(v) − Σ_S m ∫_v^x t^{s−1}/log t + f(x)G(x) − ∫_v^x f′G
        [i termini f(x)Z(x) si cancellano; Z(v) = v − log 2 + G(v)]
 6. H3 ⊢ ∫_v^x t^{s−1}/log t = A_s(x) − A_s(v) + (2/s²) W_s(x),
         A_s(t) = t^s/(s log t) + t^s/(s² log² t)                 [FTC: A_s′ = t^{s−1}/log t − 2t^{s−1}/(s² log³t)]
 7. H3 ⊢ Σ_S m x^s/(s log x) = (x^κ/log x) Σ_S m x^{iγ}/(ρ + a)            [x^s = x^κ x^{iγ}]
 8. H2, H3 ⊢ ‖Σ_S m x^s/(s² log²x)‖ ≤ K_a x^κ/log²x;  ‖Σ_S m v^s/(s² v₀²)‖ ≤ K_a v^κ/v₀²
 9. H2, H3 ⊢ ‖Σ_S m (2/s²) W_s(x)‖ ≤ 2K_a ∫_v^x t^{κ−1}/log³t ≪ x^κ/log³x          [L7 sotto]
10. H1–H3 ⊢ ‖Σ_S m v^s/(s v₀)‖ = O(1) uniformemente in T:
        1/s = 1/ρ − a/(ρ s);  Σ_S m v^ρ/ρ = Z(v) = v − log 2 + G(v) = O(1) [2];
        Σ_S m/(|ρ||s|) ≤ ½(K₀ + K_a)   [|αβ| ≤ ½(α² + β²)]
11. L7 ⊢ per b > 0, k ≥ 1, x ≥ 3: ∫_v^x t^{b−1}/log^k t ≤ C x^b/log^k x
        [se x ≤ v²: log x ≤ 2v₀; altrimenti spezzo in √x: x^{b/2} ≪ x^b/log^k x]
12. 2 ⊢ per x ≤ T: |f(x)G(x)| ≪ Y²e^{−Y/2} x^κ/log x + x^a,   x^a ≪ x^κ/log²x
        [log(xT) ≤ 2Y; x^{a+1}/T = x^κ x^{½}/T ≤ x^κ e^{−Y/2}; log²x ≪ √x]
13. 2, 11 ⊢ ‖∫_v^x f′G‖ ≪ Y²e^{−Y/2} x^κ/log x + x^κ/log²x
        [|f′(t)| ≤ K t^{a−1}/log t; ∫_v^x t^{a−1}(1 + 1/log t) ≪ x^c, c = max(a, κ/2) < κ]
14. H2 ⊢ ‖Σ_{|γ|=T} m x^{iγ}/s‖ ≤ T⁻¹ Σ_{|γ|=T} m ≪ T^{−½} = e^{−Y/2}
        [H2 con k = ⌈T⌉ − 1; per T piccolo l'insieme è in un finito fisso]
15. 5–14, M2 ⊢ Lemma A: Π_a(x) = li(x^{a+1}) − (x^κ/log x) Σ_{|γ|≤T} m x^{iγ}/(ρ+a)
                         + O_a(x^κ/log²x + Y²e^{−Y/2} x^κ/log x + 1)
        [∫_v^x f = li(x^{a+1}) − li(v^{a+1}); 2^a − li(v^{a+1}) costante]
```

## Differenze dalla prova del paper (D2)
Limite inferiore `5/2` invece di `3/2`; il salto di ψ in 2 dà il termine `2^a`; il riquadro non cambia.
La formula troncata è usata con `|γ| < T`; il passo 14 passa a `|γ| ≤ T`. `ψ₀` e `ψ` differiscono di
`≤ ½ log t` (passo 2).

## Audit
- R7: foglie in Γ₀. R8: nessun buco. R9: `x, Y, t, ρ` autovariabili; `C_G`, `K_a` da ∃E.
- R10: FOL classica, analisi di Mathlib. H1 usata solo con `t ≥ 5/2`.

**Verdetto: CHIUSA**, Γ₀ = {H1, H2, H3, M1, M2}.
