# Lemma J (autonomo)

λ = FOL classica + analisi reale (serie in ℝ).

Enunciato: per `|x| ≤ 2`, `0 ≤ J₀(x) ≤ e^{−x²/4}`, con `J₀(x) = Σ_{k≥0} (−1)^k (x/2)^{2k}/(k!)²`.
Il Teorema 4(b) resta euristico e non si formalizza; qui c'è solo il Lemma J.

## Dizionario
`y = x²/4 ∈ [0, 1]`; `a_k = y^k/(k!)²`, `b_k = y^k/k!`; `J₀(x) = Σ (−1)^k a_k`, `e^{−y} = Σ (−1)^k b_k`.

## Γ₀
- H1 (Mathlib `Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`): se `f`
  è antitona e `Σ_{i<n} (−1)^i f_i → l`, allora `Σ_{i<2k} (−1)^i f_i ≤ l ≤ Σ_{i<2k+1} (−1)^i f_i`.
- H2 serie dell'esponenziale: `Σ (−y)^n/n! = e^{−y}` (`NormedSpace.expSeries_div_hasSum_exp`, `Real.exp_eq_exp_ℝ`).
- H3 sommabilità di `(−1)^k a_k`: `|(−1)^k a_k| ≤ b_k` e `Σ b_k = e^y` (H2 con `y`).
- H4 per `y ≤ 1`: `a_{k+1} ≤ a_k` (`a_{k+1}/a_k = y/(k+1)² ≤ 1`) e `b_{k+1} ≤ b_k` (`b_{k+1}/b_k = y/(k+1) ≤ 1`).

## Albero
```
 1. J₀(x) = l_a := Σ (−1)^k a_k, convergente             [H3, (x/2)^{2k} = y^k]
 2. l_a ≥ a₀ − a₁ = 1 − y ≥ 0                            [H1 con k = 1, H4; y ≤ 1]      — prima metà
 3. l_a ≤ a₀ − a₁ + a₂ = 1 − y + y²/4                    [H1 con k = 1 (2k+1 = 3), H4]
 4. e^{−y} ≥ b₀ − b₁ + b₂ − b₃ = 1 − y + y²/2 − y³/6     [H1 con k = 2, H2, H4]
 5. 1 − y + y²/4 ≤ 1 − y + y²/2 − y³/6                    [⟺ y³/6 ≤ y²/4 ⟺ y ≤ 3/2 (o y = 0); y ≤ 1]
 6. J₀(x) ≤ e^{−y} = e^{−x²/4}                            [3, 5, 4]                     — seconda metà
```
La prima metà è quella proposta in fase 2 (A6); la seconda sostituisce la serie delle differenze
dell'audit con due somme parziali, più corte da formalizzare.

## Audit
- R7: H1–H4 (Mathlib e aritmetica). R8: nessun buco. R9: x autovariabile di ∀I.
- R10: FOL classica + analisi di Mathlib; solo assiomi standard.

**Verdetto: CHIUSA**, Γ₀ = {H1, …, H4}; nessuna ipotesi classica, nessun uso dello zero 2,404… di J₀.
