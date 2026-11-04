# Blocco C, punto 4: Teorema 3(i)

λ = FOL classica + teoria della misura di Mathlib; RH come ipotesi.

## Γ₀
- H1 `step4_assembling` (quindi `TruncatedExplicitFormula`, `RiemannVonMangoldt`, `VonKochPsi`, RH).
- H2 `AnsCor13a`: un'espansione con `r_n ≪ λ_n^{−β}`, `β > ½`, `Σ_{T<λ_n≤T+1} 1 ≪ log T` ha distribuzione limite.
- H3 `AnsThm114`: `(1/Y) ∫_0^Y φ² → c² + ½ Σ |r_n|²`.
- H4 `RiemannVonMangoldt` (C1).

## Goal
`φ(y) = E_a(e^y)` (`y ≥ log 2`, e `0` prima) ha una distribuzione limite `μ_a`, con `∫ t dμ_a = −1/(2a+1)`.
`c = −1/(2a+1)`, `λ_n` le ordinate positive distinte in ordine crescente, `ρ_n = ½ + iλ_n`, `m_n = m(ρ_n)`,
`r_n = −2 m_n/(½ + a + iλ_n)`.

## Albero
```
 1. H4 ⊢ gli zeri hanno ordinate positive illimitate; {γ ≤ T} è finito       [N(T) − F(T) = O(log T), F(T)/log T → ∞; C1]
 2. 1 ⊢ ∃ λ : ℕ → ℝ strettamente crescente, λ > 0, immagine = ordinate, λ → ∞  [ricorsione sul minimo]
 3. ⊢ m(ρ) ≥ 1 per ρ zero                                [ordine ≠ 0: analitica e nulla; ordine ≠ ⊤: ζ(2) ≠ 0, identità]
 4. H4 ⊢ m(ρ) ≪ log γ, quindi ‖r_n‖ ≪ λ_n^{−3/4}: β = ¾ > ½            [C1 su (γ−1, γ]; log γ ≤ 4γ^{¼}]
        (il paper ha β = 1 ignorando le molteplicità; per zeri semplici è la stessa cosa)
 5. 3, H4 ⊢ #{n : T < λ_n ≤ T+1} ≤ Σ_{T<γ≤T+1} m ≪ log T                                            [C1]
 6. RH ⊢ Σ_{λ_n≤X} r_n e^{iλ_n y} = −2 Σ_{0<γ≤X} m e^{iγy}/(½+a+iγ)      [n ↦ ρ_n biiezione, RH: ρ = ½ + iγ]
 7. H1, 6 ⊢ per log 3 ≤ y ≤ Y: |φ(y) − c − Re Σ_{λ_n≤e^Y} r_n e^{iλ_n y}| ≤ C(1/y + Y²e^{−Y/2})
 8. 7 ⊢ (1/Y) ∫_{log 3}^Y |…|² ≤ C²(2/(Y log 3) + 2Y⁴e^{−Y}) → 0                 [(1.7) di ANS]
 9. ⊢ φ misurabile e limitata su ogni [0, Y]          [θ_a monotona; li continua su (1, ∞)]
10. 2, 4, 5, 8, 9, H2 ⊢ ∃ μ_a, distribuzione limite di φ
11. H3 ⊢ (1/Y) ∫_0^Y φ² limitata                                                                [momenti secondi]
12. 7 ⊢ (1/Y) ∫_0^Y φ → c:
       ∫_{y₀}^Y e^{iγy} dy ≪ 1/γ; Σ m/(γ|ρ+a|) ≤ Σ m/γ² ≤ (1 + 1/(4λ₀²)) Σ m/|ρ|² < ∞ [C1];
       (1/Y)∫_{y₀}^Y (1/y + Y²e^{−Y/2}) dy ≪ (log Y)/Y + Y²e^{−Y/2} → 0
13. Lemma della media: ν_Y → μ debolmente, momenti secondi ≤ B ⟹ primi momenti convergenti:
       con f_M(t) = max(−M, min(t, M)): |t − f_M(t)| ≤ t²/M;
       ∫ min(t², M) dμ ≤ B ⟹ ∫ t² dμ ≤ B  [convergenza monotona];
       |c − ∫ t dμ| ≤ 2B/M per ogni M > 0
14. 10–13 ⊢ ∫ t dμ_a = −1/(2a+1)
```
La media è dimostrata (passi 12–13), non assunta: ANS la citano solo di passaggio. Il passo 12 non usa la
quasi-periodicità `B²`, usa direttamente lo Step 4 (più diretto del testo del paper, stessa conclusione).

## Audit
- R7: foglie in Γ₀. R8: nessun buco. R9: `Y, y, M, n` autovariabili. R10: FOL classica e misura.

**Verdetto: CHIUSA**, Γ₀ = {H1–H4}.
