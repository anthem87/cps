# Blocco C, punto 3b: Teorema 3, Step 4 (assemblaggio)

λ = FOL classica + analisi di Mathlib; RH come ipotesi.

## Γ₀
- H1 `lemmaA` (da `TruncatedExplicitFormula`, `RiemannVonMangoldt`, RH).
- H2 `step2_bias_layer` (da `VonKochPsi`, RH).
- H3 `layersR_le` (Step 3, incondizionato), `piA_eq_layers`.
- H4 `riemannZeta_ne_zero_of_real`: `ζ(½) ≠ 0` (dimostrato, `ZetaReal`).
- H5 `riemannZeta_conj`, `zeroMult_conj`.

## Goal
Per `Y ≥ 2`, `T = e^Y`, `log 3 ≤ y ≤ Y`:
`E_a(e^y) = −1/(2a+1) − 2 Re Σ_{0<γ≤T} e^{iγy}/(½ + a + iγ) + ε_a(y, T)`, con `|ε_a(y, T)| ≪_a 1/y + Y²e^{−Y/2}`.

## Albero
```
 1. H4, RH ⊢ nessuno zero non banale ha γ = 0                     [γ = 0 ⟹ ρ = ½]
 2. RH ⊢ ρ + a = ½ + a + iγ; x^{iγ} = e^{iγy} per x = e^y
 3. H5 ⊢ g(ρ̄) = conj g(ρ), m(ρ̄) = m(ρ), dove g(ρ) = e^{iγy}/(½ + a + iγ)
 4. 1, 2, 3 ⊢ Σ_{|γ|≤T} m x^{iγ}/(ρ+a) = 2 Re Σ_{0<γ≤T} m g(ρ)       [ρ ↦ ρ̄ biiezione tra γ > 0 e γ < 0]
 5. H2 ⊢ |½θ_{2a}(√x) − x^κ/((2a+1) log x)| ≤ C₂ x^κ/log²x per ogni x ≥ 3
        [O a +∞; sul compatto [3, x₀] il primo membro è limitato e x^κ/log²x ≥ 1/log²x₀]
 6. H3 ⊢ θ_a = Π_a − ½θ_{2a}(√x) − R
 7. 4, 5, 6, H1, H3 ⊢ (θ_a − li(x^{a+1})) log x/x^κ + 1/(2a+1) + 2 Re Σ_{0<γ≤T} m g(ρ) =
        (e_A − e₂ − R) log x/x^κ,
        ‖e_A‖ ≤ C_A (x^κ/log²x + Y²e^{−Y/2} x^κ/log x + 1), |e₂| ≤ C₂ x^κ/log²x, 0 ≤ R ≤ C₃ x^κ/log²x
 8. ⊢ log x/x^κ ≤ D/log x                       [log²x ≪ x^κ]
 9. 7, 8 ⊢ |ε_a| ≤ (C_A + C₂ + C₃ + C_A D)/y + C_A Y²e^{−Y/2}
```

## Audit
- R7: foglie in Γ₀. R8: nessun buco. R9: `Y, y, ρ` autovariabili. R10: FOL classica, analisi di Mathlib.

**Verdetto: CHIUSA**, Γ₀ = {H1–H5} (quindi `TruncatedExplicitFormula`, `RiemannVonMangoldt`, `VonKochPsi`, RH).
