# Numerici: fatti interi, Tabella 1, primo attraversamento a x = 109

λ = FOL classica con l'aritmetica del kernel (`decide +kernel`, senza `native_decide`). Fuori da `Table1Cert`, nessuna ipotesi.

## Γ₀
H1 `Table1Cert`, solo per `table1_crossing`: certificato Arb, ipotesi esplicita con nome e script.

## 1. Fatti interi (`grid_integers`, `first_crossing_table`, `table1_primes`)
```
 1. primeB n = true ⟺ n primo                                 [trial division fino a √n; trialOk_iff, Nat.prime_def_le_sqrt]
 2. S N = sumLoop (N+1) 0 1                                    [induzione su Ico]
 3. S 10, S 100, S 1000, S 10000, S 4691; S 103, …, S 127       [kernel, 1 e 2]
 4. Lucas: a^(p−1) ≡ 1, a^((p−1)/q) ≢ 1 per q | p−1, e (p−1) fattorizzato ⊢ p primo   [lucas_primality; powMod_cast]
 5. N₁, …, N₂₀ primi: certificati ricorsivi; i fattori < 10⁶ con norm_num   [gen_numerics.py]
```
`S(N_n)` per `n ≥ 2` non si calcola nel kernel: resta nel certificato. Il costo del blocco è circa 2 minuti di compilazione.

## 2. Tabella 1 (`Table1Cert`, `table1_crossing`)
Per ogni riga `(n, lo, hi, N)`, con `m = π(N)`: esiste `γ` ordinata con `N(γ) = n` (`zeroCount`), `lo/10²⁴ < γ < hi/10²⁴`,
`σ_{m−1} < lo/10²⁴`, `hi/10²⁴ ≤ σ_m`. Dal certificato si dimostra `firstCrossing γ = N`:
```
 6. γ ≤ σ_m = log S N ⊢ N(γ) ≤ N                              [prime_primeCounting, firstCrossing_le]
 7. q := N(γ) < N ⊢ π(q) ≤ m − 1 ⊢ q ≤ p_{m−1} ⊢ log S q ≤ σ_{m−1} < γ: assurdo   [S_mono, firstCrossing_mem]
```
Script: `02_certify.py` (Zenodo 10.5281/zenodo.23269807; Arb 400 bit, primesum), output `run.jsonl`. Gli intervalli razionali vengono da
`scripts/numerics/certify_table1.py` (Arb 400 bit), output `scripts/numerics/table1_cert.txt`.

## 3. Primo attraversamento (`first_crossing_a1`)
Goal: `IsLeast {x | 2 ≤ x ∧ li(x^{1+1}) < θ₁(x)} 109`. Margini (mpmath): minimo `0,72` a `p = 3`, `1,21` a `p = 7`; a `x = 109`, `+31,6`.
```
 8. 1/log u − 1/(u−1) ≥ ½ su (0,1)                             [log(1+w) ≥ 2w/(w+2)]
 9. li 2 = ∫_0^2 h, 0 ≤ h ≤ 1, 8 ⊢ ½ ≤ li 2 ≤ 2                 [li_eq]
10. (b−a)/c ≤ li b − li a se log b ≤ c; li b − li a ≤ (b−a)/c se 0 < c ≤ log a   [valor medio, hasDerivAt_li]
11. y⁶⁴ ≤ 2^m ⊢ log y ≤ (m/64) log 2 < (m/64)·0,6931471808; simmetrico      [Real.log_two_lt_d9, log_two_gt_d9]
12. griglia di 156 punti (rapporto 1,07, con tutti i p², p ≤ 109): L/10⁴ ≤ li(y) ≤ U/10⁴   [liChain_sound, liChainOk nel kernel]
13. ∀ n ∈ [2, 109): ∃ punto y ≤ n², (S n − 1)·10⁴ < L             [kernel]
14. 2 ≤ x < 109, n = ⌊x⌋: θ₁(x) = S n − 1 < L/10⁴ ≤ li(y) ≤ li(x²)   [13, li crescente]
15. li(109²) ≤ 1455,78 < 1480 = θ₁(109)                         [12]
```
Il margine basta: **nessun certificato**. Solo `x ≥ 2`: per `x` appena sopra `1`, `li(x²) < 0 = θ₁(x)`, e il paper definisce `E_a` per `x ≥ 2`.

## Audit
R7: foglie in Γ₀ o lemmi dimostrati. R8: nessun buco. R9: nessuna variabile libera. R10: `#print axioms` dà gli assiomi standard: `decide +kernel` non aggiunge assiomi.

**Verdetto: CHIUSA**; Γ₀ = ∅ per 1 e 3, Γ₀ = {H1} per 2.
