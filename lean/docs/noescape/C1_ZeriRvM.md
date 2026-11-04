# Blocco C, punto 1: conseguenze di Riemann–von Mangoldt

λ = FOL classica + analisi complessa di Mathlib.

## Γ₀
- H1 `RiemannVonMangoldt`: `N(T) = F(T) + E(T)`, `F(T) = (T/2π) log(T/2π) − T/2π`, `|E(T)| ≤ C log T`
  per `T ≥ T₀`.
- M1 Mathlib `IsCompact.inter_riemannZetaZeros_finite`: un compatto contiene finiti zeri di ζ.
- M2 Mathlib `riemannZeta_conj`: `ζ(s̄) = conj ζ(s)`.
- M3 Mathlib, ordine analitico: `ord_{z₀} f = n ⟺ f = (z − z₀)^n g` vicino a `z₀`, `g` analitica,
  `g(z₀) ≠ 0`; analitica ⟺ olomorfa su un intorno.

## Goal
- (G1) `Σ_{T<γ≤T+1} m(ρ) ≪ log T` per `T → ∞`.
- (G2) `Σ_ρ m(ρ)/|ρ + a|² < ∞` per ogni reale `a`, sugli zeri non banali.

## Albero
```
 1. ⊢ {ρ ∈ Z : |γ| ≤ T} finito                     [M1, Z ∩ B̄(0, 1 + |T|); |ρ| ≤ |β| + |γ|]
 2. ⊢ N(T+1) = N(T) + Σ_{T<γ≤T+1} m(ρ)            [1; unione disgiunta di insiemi finiti]
 3. ⊢ F(T+1) − F(T) ≤ (1/2π)(log(T+1) + 1)          [(T+1)log(T+1) − T log T = log(T+1) + T log(1 + 1/T),
                                                      T log(1 + 1/T) ≤ 1]
 4. H1 ⊢ Σ_{T<γ≤T+1} m ≤ (1/2π)(log(T+1)+1) + C log(T+1) + C log T ≪ log T     (G1)   [2, 3]
 5. ⊢ ρ ∈ Z ⟹ ρ̄ ∈ Z e m(ρ̄) = m(ρ)                 [M2; M3 con g ↦ conj ∘ g ∘ conj]
 6. ⊢ Σ_{T<|γ|≤T+1} m = 2 Σ_{T<γ≤T+1} m  (T ≥ 0)    [5: ρ ↦ ρ̄ biiezione tra le due metà]
 7. ⊢ per k ≥ 1 e |γ| > k: |ρ + a| ≥ |γ| > k          [|Im(ρ + a)| = |γ|]
 8. H1 ⊢ per ogni finito s ⊆ Z:
       Σ_{ρ∈s} m/|ρ+a|² ≤ Σ_{|γ|≤K} m/|ρ+a|² + Σ_{k≥K} 2 C′ log(k+1)/k²      [6, 7, 4]
 9. H1 ⊢ (G2)                                         [8; serie a termini ≥ 0 con somme parziali limitate]
```

## Audit
- R7: foglie in Γ₀ ∪ {M1–M3}. R8: nessun buco. R9: T, a, k, s autovariabili.
- R10: FOL classica, analisi di Mathlib.

**Verdetto: CHIUSA**, Γ₀ = {H1, M1, M2, M3}.
