# Blocco D, punto 1: Teorema 3(ii)

λ = FOL classica + teoria della misura di Mathlib; RH e LI come ipotesi nominate (antecedenti).

## Γ₀
- H1 `RiemannHypothesis`, H2 `LI` (congettura, solo antecedente).
- H3 `step4_assembling` via `ansExpansion_phiA`, quindi `TruncatedExplicitFormula`, `RiemannVonMangoldt`, `VonKochPsi`.
- H4 `AnsThm19`: `∫ e^{−iξt} dμ = e^{−icξ} Π_n J₀(|r_n ξ|)` per ogni distribuzione limite `μ`.
- H5 `BesselDecay`: `|J₀(x)| ≤ C/√|x|` per `|x| ≥ 1`.
- H6 `RubinsteinSarnakInversion`: `ν` simmetrica con `ν̂` integrabile ⟹ `ν(b,∞) = ½ − (1/π)∫_0^∞ sin(bξ)/ξ ν̂(ξ) dξ`, `b > 0`.
- `μ` una qualsiasi distribuzione limite di `φ = phiA a` (esiste per il Teor. 3(i)), `a > −½`.

## Dizionario
`κ = a + ½`, `c = −1/(2a+1)`, `b = 1/(2a+1) = −c > 0`; `d(γ) = |κ + iγ|`;
`P(ξ) = Π_{γ>0} J₀(2ξ/d(γ))` (`prodJ`), `δ_a = ½ − (1/π)∫_0^∞ sin(bξ)/ξ · P(ξ) dξ` (`deltaA`).
Densità logaritmica di `S`: `(1/log X) ∫_2^X 1_S(x) dx/x → d` (`HasLogDensity`).

## Goal
`μ ≪ Leb`; `μ` simmetrica attorno a `c`; `{θ_a > li(x^{a+1})}` ha densità logaritmica `δ_a`.
Più due enunciati di buona definizione: il prodotto è moltiplicabile e l'integrando è integrabile
(così `∏'` e `∫` non sono valori di comodo).

## Albero
```
Bessel
 1. ⊢ ansJ0 z = J₀(z)                [exp in serie, integrazione termine a termine; ∫_0^1 cos^{2k}(2πt) = C(2k,k)/4^k
                                       (riduzione integral_cos_pow), potenze dispari nulle]
 2. 1 ⊢ |J₀(x)| ≤ 1; J₀(−x) = J₀(x)              [norma dell'integrale ≤ 1; potenze pari]
 3. Lemma J, serie alternante ⊢ per |x| ≤ 2: 1 − x²/4 ≤ J₀(x) ≤ e^{−x²/4}
 4. 2, 3 ⊢ ∀x |J₀(x) − 1| ≤ x²/2 e |J₀(x) − e^{−x²/4}| ≤ x⁴/8     [|x| ≤ 2: 3 con e^{−y} ≤ 1−y+y²/2; |x| > 2: ≤ 2]

Prodotto
 5. RH, RvM ⊢ Σ_n 1/d(λ_n)² < ∞                    [sum_zeros_le, ρ = ½ + iλ_n, ‖ρ + a‖ = d(λ_n), m ≥ 1]
 6. 4, 5 ⊢ Σ_n |J₀(2ξ/d(λ_n)) − 1| < ∞ ⟹ multipliable; enumerazione λ ⟹ Π_{n<N} → P(ξ)
 7. LI ⊢ m_n = 1, quindi |r_n ξ| = 2|ξ|/d(λ_n); LI ⟹ λ linearmente indipendente su ℚ [comp con ℕ ≃ ordinate]
 8. H3, H4, 1, 2, 6, 7 ⊢ ∫ e^{iξt} dμ = e^{icξ} P(ξ)      [unicità del limite; H4 in −ξ]

Parte simmetrica
 9. ν := μ traslata di −c. 8 ⊢ ν̂(ξ) = P(ξ) ∈ ℝ, pari        [charFun_map_add_const]
10. 9 ⊢ ν.map(−) = ν                                       [Measure.ext_of_charFun]
    ⟹ μ.map(t ↦ 2c − t) = μ

Decadimento
11. 2, 6 ⊢ |P(ξ)| ≤ |Π_{n<N} J₀(2ξ/d(λ_n))|                [fattori di coda ≤ 1; passaggio al limite]
12. H5, 11 ⊢ ∀N ∃K, ξ₀: |ξ| ≥ ξ₀ ⟹ |P(ξ)| ≤ K (√|ξ|)^{−N}   [ξ₀ = max d(λ_n)/2, n<N; C ≥ 0 da x = 1]
13. 12 (N=4), |P| ≤ 1 ⊢ |P(ξ)| ≤ K′/(1+ξ²), quindi ν̂ integrabile

Inversione e assoluta continuità
14. H6, 10, 13 ⊢ per b′ > 0: F(b′) := ν(b′,∞) = ½ − (1/π)∫_0^∞ sin(b′ξ)/ξ P(ξ) dξ
15. M := (1/π)∫_0^∞ |P|. 14, |sin u − sin v| ≤ |u−v|, |sin u| ≤ |u| ⊢
       0 < p < q ⟹ ν(p,q] ≤ M(q−p);  |F(p) − ½| ≤ Mp
16. 15, 10 ⊢ ν(0,∞) ≥ ½, ν(−∞,0) = ν(0,∞), totale 1 ⟹ ν{0} = 0 e ν(0,∞) = ½; ν(0,q] ≤ Mq
17. 15, 16, 10 ⊢ ∀u<v: ν(u,v] ≤ M(v−u)                      [per segno; v ≤ 0: riflessione e {p} trascurabile]
18. 17 ⊢ M·x − cdf_ν(x) è monotona e continua a destra: funzione di Stieltjes S;
       M·Leb = ν + S.measure                                  [Measure.ext_of_Ioc]
    ⟹ ν ≤ M·Leb ⟹ ν ≪ Leb ⟹ μ ≪ Leb                       [traslazione]

Densità
19. Lemma: φ misurabile, μ limite di φ, μ{0} = 0 ⟹ (1/Y)∫_0^Y 1[φ>0] → μ(0,∞)
       [f_k(t) = rampa(kt) ≤ 1[t>0] ≤ g_k(t) = rampa(kt+1); convergenza dominata per ∫f_k dμ, ∫g_k dμ;
        il bordo {0} ha misura nulla]
20. μ(0,∞) = ν(b,∞) = δ_a                                [t − c > −c ⟺ t > 0; 14 con b′ = b, ν̂ = P]
21. y ≥ log 2 ⟹ (φ(y) > 0 ⟺ θ_a(e^y) > li(e^{(a+1)y}))      [peso y/e^{κy} > 0]; y < log 2 ⟹ φ(y) = 0
22. x = e^y: ∫_2^X 1_S(x) dx/x = ∫_{log 2}^{log X} 1_S(e^y) dy  [integral_image_eq_integral_abs_deriv_smul]
23. 19–22, log X → ∞ ⊢ HasLogDensity S δ_a
```

## Nota sul percorso
Il paper deduce l'assoluta continuità da "μ̂ integrabile" (fatto standard; Mathlib non ha l'inversione per
misure). Qui passa per H6 (passi 14–18), che è già tra le ipotesi: nessuna ipotesi aggiunta.
Il paper scrive `μ_a` come legge di `X_a` con `U_γ` i.i.d.; il Lean non costruisce lo spazio prodotto: la
funzione caratteristica di H4 basta per tutto l'enunciato.

## Audit
- R7: foglie in Γ₀ o lemmi di Mathlib. R8: nessun buco. R9: `ξ, N, p, q, u, v, k, X` autovariabili.
- R10: FOL classica e misura; RH e LI solo antecedenti, mai negati.

**Verdetto: CHIUSA**, Γ₀ = {H1–H6}.
