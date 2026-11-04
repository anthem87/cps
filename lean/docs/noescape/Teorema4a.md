# Blocco D, punto 2: Teorema 4(a)

λ = FOL classica + teoria della misura di Mathlib; RH e LI come ipotesi nominate.

## Γ₀
- H1 Teorema 3(ii) (`RiemannHypothesis`, `LI`, `TruncatedExplicitFormula`, `RiemannVonMangoldt`, `VonKochPsi`,
  `AnsThm19`, `BesselDecay`, `RubinsteinSarnakInversion`).
- H2 `AnsCor13a`: esistenza di `μ_a`.
- H3 `RiemannVonMangoldt`: `N(T) = F(T) + O(log T)`, `F(T) = (T/2π)(log(T/2π) − 1)`.
- Da Mathlib: continuità di Lévy (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`), portmanteau, gaussiana.

## Dizionario
`A = a + ½`; `σ_a² = Σ_{γ>0} 2/(A²+γ²)` (`sigmaSq`, sotto LI gli zeri sono semplici); `ρ_γ = 2/√(A²+γ²)`, `Σρ_γ² = 2σ_a²`;
`b_a = 1/(2A)`; `ν_a` la parte simmetrica del Teor. 3(ii), `ν̂_a = P_a`.

## Goal
(1) `σ_a² ∼ log(A/2π)/(2A)` per `a → ∞`.  (2) `δ_a → ½` per `a → ∞`.

## Albero, (1)
```
 1. −f′_A(t) = g_A(t) := 4t/(A²+t²)², f_A(t) = 2/(A²+t²)      ⟹ f_A(λ) = ∫_λ^∞ g_A      [FTC impropria]
 2. Σ_n f_A(λ_n) = ∫_0^∞ N(t) g_A(t) dt                      [hasSum_integral_of_summable_integral_norm; Σ_n 1[λ_n ≤ t] = N(t) con LI]
 3. H3 ⊢ ∃C ∀t ≥ 0: |N(t) − F(t)| ≤ C(1 + √t)                [t grande: O(log t) ≤ √t; t piccolo: N, F limitate]
 4. ∫_0^∞ (1+√t) g_A(t) dt ≤ K A^{−3/2}, A ≥ 1                [t = Au]
 5. ∫_0^∞ F(t) g_A(t) dt = (2/(πA)) [(log(A/2π) − 1) c₁ + c₂]  [t = Au, integral_comp_mul_left_Ioi]
       c₁ = ∫_0^∞ u²/(1+u²)² du = π/4  [primitiva ½(arctan u − u/(1+u²))]
       c₂ = ∫_0^∞ u² log u/(1+u²)² du finito  [≤ 1 su (0,1]; ≤ 2u^{−3/2} su (1,∞)]
 6. 2–5 ⊢ σ_a² = log(A/2π)/(2A) + O(1/A)
 7. log(A/2π)/(2A) · A → ∞ ⟹ σ_a² ∼ log(A/2π)/(2A)
```
Il valore esatto `c₂ = π/4` non serve (il paper non lo usa: gli basta l'asintotico).

## Albero, (2)
```
 8. 7 ⊢ A²σ_a² → ∞                                             [A²σ² ∼ A log(A/2π)/2]
 9. x_γ := ρ_γ ξ/σ_a: Σx_γ² = 2ξ²; x_γ² ≤ 4ξ²/(A²σ²)
10. |J₀(x) − e^{−x²/4}| ≤ x⁴/8, |J₀| ≤ 1, |e^{−x²/4}| ≤ 1 (Teor. 3(ii), passo 4) ⟹ telescopica:
       |Π_{n<N} J₀(x_n) − e^{−Σ_{n<N} x_n²/4}| ≤ Σ_{n<N} x_n⁴/8
11. N → ∞, 9 ⊢ |P_a(ξ/σ_a) − e^{−ξ²/2}| ≤ (1/8)(4ξ²/(A²σ²))(2ξ²) = ξ⁴/(A²σ²) → 0
12. Lévy ⊢ per ogni a_n → ∞: ν_{a_n}∘(·/σ_{a_n}) → N(0,1) debolmente     [charFun_map_mul, charFun_gaussianReal]
13. δ_a = ν_a(b_a,∞) = (ν_a∘/σ_a)(b_a/σ_a,∞)                 [Teor. 3(ii), passi 14, 20]
14. (b_a/σ_a)² = 1/(4A²σ²) → 0                                 [8]
15. Limite superiore: b_a/σ_a > 0 ⟹ δ_a ≤ (ν_a∘/σ_a)(0,∞) = ½    [Teor. 3(ii), passo 16]
16. Limite inferiore: ∀ε>0 definitivamente b_a/σ_a < ε, quindi δ_a ≥ (ν_a∘/σ_a)(ε,∞) → N(ε,∞);
       N(ε,∞) → N(0,∞) = ½ per ε ↓ 0                            [portmanteau: bordo {ε} nullo; simmetria e assenza di atomi]
17. 15, 16 ⊢ δ_a → ½
```
Il passaggio "Pólya" del paper (convergenza uniforme delle ripartizioni verso un limite continuo) è qui il
sandwich 15–16, che ne dimostra la parte che serve: ripartizioni valutate in punti `b_a/σ_a → 0`.

## Differenza dal testo del paper
Il paper cita Lindeberg. Qui 9–12 dimostrano direttamente la convergenza delle funzioni caratteristiche
(decisione di Antonio, 4 novembre 2026); `LindebergFeller` non è più nel progetto. Vedi DIVERGENZE.md.

## Audit
- R7: foglie in Γ₀ o lemmi di Mathlib. R8: nessun buco. R9: `t, u, ξ, ε, N, n` autovariabili.
- R10: FOL classica e misura; RH e LI solo antecedenti.

**Verdetto: CHIUSA**, Γ₀ = {H1–H3}.
