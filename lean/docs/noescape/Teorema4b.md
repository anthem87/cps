# Blocco E: Teorema 4(b) (Lemma J, Lemma W, conclusione)

λ = FOL classica + teoria della misura di Mathlib; RH e LI come ipotesi nominate.

## Γ₀
- H1 `RiemannHypothesis`, H2 `LI`.
- H3 `RiemannVonMangoldt`: `N(T) = F(T) + O(log T)`, `F(T) = (T/2π)(log(T/2π) − 1)`.
- H4 `BesselDecay`: `|J₀(x)| ≤ C/√|x|` per `|x| ≥ 1`.
- Solo per l'identificazione probabilistica (`half_sub_deltaA_eq`), non per l'asintotica: le ipotesi del Teorema 3(ii)
  (`TruncatedExplicitFormula`, `VonKochPsi`, `AnsThm19`, `RubinsteinSarnakInversion`).
- Già dimostrati (Blocco D): `lemmaJ`, `ansJ0_eq`, `abs_prodJ_sub_exp_le`, `abs_prodJ_le_prod`, `exists_prodJ_le_inv`,
  `sigmaSq_isEquivalent`, `tendsto_sq_mul_sigmaSq`, `exists_zeroCount_sub_le`, `hasSum_zeroCount`.

## Dizionario
`A = a + ½`; `L = log(A/2π)`; `σ = σ_a = √(sigmaSq a)`; `D_γ = |A + iγ| = zeroDen a γ`; `P_a(ξ) = Π_γ J₀(2ξ/D_γ) = prodJ a ξ`.

**Lo shift.** `μ_a` è simmetrica attorno a `b′ = −1/(2a+1) = −1/(2A)` (Teorema 3). Poniamo `b_a = −b′ = 1/(2A)` e
`W = (X_a − b′)/σ`, che è simmetrica con funzione caratteristica `s ↦ P_a(s/σ)`. Allora
`δ_a = P(X_a > 0) = P(W > −b′/σ) = P(W > h_a)`, con `h_a = b_a/σ = 1/(2Aσ) > 0`.

## Goal
(W) `∫_0^∞ |P_a(s/σ) − e^{−s²/2}| ds → 0`, e quindi, uniformemente in `z`,
`f_a(z) := (1/π)∫_0^∞ cos(zs) P_a(s/σ) ds → (2π)^{−1/2} e^{−z²/2}`.
(4b) `½ − δ_a ∼ b_a/(σ√(2π))` e `½ − δ_a ∼ 1/(2√(π A L))`.

## Lemma J (già in `CpsLean/Bessel`)
Per `|x| ≤ 2`, cioè `y = x²/4 ≤ 1`: `0 ≤ J₀(x) ≤ e^{−y}`.

La prova del Lean usa le somme parziali delle due serie alternanti:
`1 − y ≤ J₀(x) ≤ 1 − y + y²/4` e `e^{−y} ≥ 1 − y + y²/2 − y³/6 ≥ 1 − y + y²/4`.

La forma equivalente è sulla differenza. Con `c_k = y^k/k! − y^k/(k!)² = (y^k/k!)(1 − 1/k!)` si ha
`e^{−y} − J₀(x) = Σ_{k≥2} (−1)^k c_k`, con `c₂ = y²/4`, `c₃ = 5y³/36` e, per `k ≥ 2`, il rapporto generale

    c_{k+1}/c_k = y/(k+1) · (1 − 1/(k+1)!)/(1 − 1/k!).

Il secondo fattore vale `5/3` per `k = 2` e decresce poi (`23/20` per `k = 3`), quindi è `≤ 5/3`; con `k + 1 ≥ 3` si ottiene
`c_{k+1}/c_k ≤ 5y/9 < 1`. La serie è alternante a termini decrescenti e la sua somma è `≥ 0`.

## Albero, θ
```
 1. J₀(x) = ∫_0^1 cos(x cos 2πt) dt                                       [ansJ0_eq, parte reale]
 2. x ≠ 0, v = min(|x|, 1), t₀ = arccos(v/x)/2π ∈ [0,1]: x cos 2πt₀ = v, 0 < v ≤ 1 < π ⊢ |cos v| < 1
 3. 1, 2, integrandi 1 ∓ cos(x cos 2πt) ≥ 0 continui, > 0 in t₀ ⊢ |J₀(x)| < 1   [intervalIntegral.integral_pos]
 4. J₀ continua                                                           [1, integrale parametrico]
 5. H4 ⊢ ∃R ≥ √2: |u| ≥ R ⇒ |J₀(u)| ≤ ½
 6. 3, 4: |J₀| ha massimo M < 1 sul compatto [√2, R]                       [IsCompact.exists_isMaxOn]
 7. θ := max(½, M) < 1 ∧ ∀u, √2 ≤ |u| ⇒ |J₀(u)| ≤ θ                        [J₀ pari]
```
Nessun valore numerico di `θ`; nessuna ipotesi oltre H4.

## Albero, Lemma W
Zona centrale, `|ξ| ≤ A`:
```
 8. D_γ ≥ A ⊢ |2ξ/D_γ| ≤ 2
 9. 8, Lemma J: 0 ≤ J₀(2ξ/D_γ) ≤ e^{−ξ²/D_γ²}; Σ_γ ξ²/D_γ² = ξ²σ²/2 ⊢ 0 ≤ P_a(ξ) ≤ e^{−ξ²σ²/2}
10. ξ = s/σ: per 0 < s ≤ Aσ, |P_a(s/σ) − e^{−s²/2}| ≤ 2e^{−s²/2}
```
Coda, `|ξ| ≥ A`:
```
11. H3, exists_zeroCount_sub_le: N(A) ≥ A definitivamente
12. 11, hasSum_zeroCount (LI): per K = ⌊A⌋ (≤ #{0 < γ ≤ A}), λ_n ≤ A per n < K
13. n < K ⊢ D_n² ≤ 2A² ⊢ x_n = 2|ξ|/D_n ≥ √2 |ξ|/A ≥ √2
14. 7, 13: |J₀(x_n)| ≤ θ;   H4, 13: |J₀(x_n)| ≤ C/√(√2|ξ|/A), quindi il prodotto di 4 fattori è ≤ C⁴A²/(2ξ²)
15. abs_prodJ_le_prod, 14: |P_a(ξ)| ≤ θ^{K−4} C⁴ A²/(2ξ²)
16. ξ = s/σ, ∫_{Aσ}^∞ ds/s² = 1/(Aσ) ⊢ ∫_{Aσ}^∞ |P_a(s/σ)| ds ≤ C⁴ · Aσ · θ^{K−4}/2
17. σ → 0, K = ⌊A⌋ ⊢ Aσθ^{K−4} → 0                                         [tendsto_self_mul_const_pow_of_lt_one]
```
Unione:
```
18. g_a(s) = |P_a(s/σ) − e^{−s²/2}|. g_a(s) ≤ s⁴/(A²σ²) → 0 per ogni s          [abs_prodJ_sub_exp_le, A²σ² → ∞]
19. d_a = min(g_a, 2e^{−s²/2}): dominata da 2e^{−s²/2}, → 0 ⊢ ∫_0^∞ d_a → 0     [convergenza dominata]
20. T_a(s) = 1[s > Aσ]|P_a(s/σ)|: 10 ⊢ g_a ≤ d_a + T_a su (0,∞)                 [in s > Aσ, g_a ≤ |P_a| + e^{−s²/2}]
21. 16, 17, 19, 20 ⊢ (W), parte L¹
22. |f_a(z) − (1/π)∫_0^∞ cos(zs)e^{−s²/2} ds| ≤ (1/π)∫_0^∞ g_a, per ogni z
23. ∫_0^∞ cos(zs)e^{−s²/2} ds = √(π/2) e^{−z²/2}                               [fourierIntegral_gaussian, parità]
24. 21, 22, 23 ⊢ (W), uniforme in z
```

## Albero, Teorema 4(b)
```
25. ½ − δ_a = (1/π)∫_0^∞ sin(b_a ξ)/ξ · P_a(ξ) dξ                               [definizione di deltaA]
26. ξ = s/σ: ½ − δ_a = (h_a/π)∫_0^∞ sinc(h_a s) P_a(s/σ) ds                     [integral_comp_mul_left_Ioi]
27. |∫_0^∞ sinc(h_a s)(P_a(s/σ) − e^{−s²/2}) ds| ≤ ∫_0^∞ g_a → 0                [|sinc| ≤ 1, 21]
28. h_a → 0, sinc continua, |sinc| ≤ 1 ⊢ ∫_0^∞ sinc(h_a s) e^{−s²/2} ds → √(π/2) [convergenza dominata]
29. 26–28 ⊢ (½ − δ_a)/h_a → (1/π)√(π/2) = (2π)^{−1/2}
30. 29 ⊢ ½ − δ_a ∼ b_a/(σ√(2π))
31. [b_a/(σ√(2π))]² · 4πAL = L/(2Aσ²) → 1                                       [sigmaSq_isEquivalent]
32. 30, 31 ⊢ ½ − δ_a ∼ 1/(2√(πAL))
```
Identificazione con la legge (ipotesi del Teorema 3(ii) in più):
```
33. δ_a = ν(b_a, ∞), ν(0, ∞) = ½, ν({0}) = 0     [deltaA_eq, real_shiftLaw_Ioi, real_singleton_zero_and]
34. ½ − δ_a = ν(0, b_a] = P(0 < W ≤ h_a), W = (X_a − b′)/σ, b′ = −1/(2A)
```
Il passaggio 26–29 è la forma integrata di `P(0 < W ≤ h_a) = ∫_0^{h_a} f_a(z) dz = h_a((2π)^{−1/2} + o(1))`: si ha
`∫_0^h cos(zs) dz = h sinc(hs)`. Passare da `sinc` evita Fubini e non chiede che `f_a` sia già riconosciuta come densità.

## Audit
- R7: foglie in Γ₀ o lemmi già dimostrati.
- R8: nessun buco. R9: `a, s, ξ, z, t, n` autovariabili.
- R10: FOL classica più Mathlib. RH e LI restano ipotesi. LI serve per `sigmaSq_isEquivalent` e al passo 12 (zeri semplici).
- La prova dell'asintotica non usa `μ_a`: usa la formula di `δ_a`. Il legame con la densità logaritmica è il Teorema 3(ii).
- Il paper dichiara (b) "Heuristic": qui è dimostrato sotto RH ∧ LI. Il paper non si tocca (DIVERGENZE).

**Verdetto: CHIUSA**, Γ₀ = {RH, LI, RiemannVonMangoldt, BesselDecay}; per `half_sub_deltaA_eq` anche le ipotesi del Teorema 3(ii).
