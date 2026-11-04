# Blocco D, punto 3: Osservazione 1 (punto critico `a = −½`, parte deterministica)

λ = FOL classica; nessuna ipotesi su RH.

## Γ₀
H1 `Mertens2`: `Σ_{p≤x} 1/p = log log x + B + O(1/log x)`. Usata solo nella quarta parte.

## Dizionario
`B_a(x) = ½ ∫_2^{√x} t^{2a}/log t dt` (`biasTerm`).

## Goal
(i) `a > −½`: `B_a(x) ∼ x^{a+½}/((2a+1) log x)`.
(ii) `x ≥ 4`: `B_{−½}(x) = ½(log log √x − log log 2)`.
(iii) `B_{−½}(x) = ½ log log x + O(1)`.
(iv) (Mertens) `½ Σ_{p≤√x} 1/p = ½ log log x + O(1)`.

## Albero
```
 1. G(t) = t^{b+1}/((b+1) log t), G′ = t^b/log t − t^b/((b+1) log²t)                [hasDerivAt_G]
 2. b = 2a > −1: ∫_2^y t^b/log t = G(y) − G(2) + (b+1)⁻¹ ∫_2^y t^b/log²t            [FTC]
 3. ∫_2^y t^b/log²t ≤ √y^{b+1}/((b+1)log²2) + 4y^{b+1}/((b+1)log²y)     [integral_rpow_div_log_sq_le]
 4. 2, 3 ⊢ ∫_2^y t^b/log t − G(y) = O(y^{b+1}/log²y) = o(G(y))
 5. y = √x, y^{2a+1} = x^{a+½}, log y = ½ log x ⊢ (i)                   [½ G(√x) = x^{a+½}/((2a+1) log x)]
 6. (log log t)′ = 1/(t log t), t^{−1} = t^{2·(−½)} ⊢ (ii)              [FTC su [2, √x], x ≥ 4]
 7. log log √x = log(½ log x) = log log x − log 2 ⊢ B_{−½}(x) − ½ log log x = −½ log 2 − ½ log log 2 ⊢ (iii)
 8. H1 in √x, 7 ⊢ ½Σ_{p≤√x}1/p − ½ log log x = ½(B − log 2) + O(1/log x) = O(1) ⊢ (iv)
```

## Audit
- R7: foglie in Γ₀ o lemmi già dimostrati. R8: nessun buco. R9: `x, y, t` autovariabili.
- R10: FOL classica. RH non compare: il paper dice "Unconditionally".
- Lo "Status" del paper lascia l'enunciato completo sul termine degli zeri "at the level of a remark": non si formalizza.

**Verdetto: CHIUSA**, Γ₀ = {H1}.
