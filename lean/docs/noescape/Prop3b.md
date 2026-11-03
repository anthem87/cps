# Proposizione 3(b) (ripple ⇒ RH)

λ = FOL classica + analisi reale e complessa (come in Mathlib).

Enunciato: se `S(x) − B(x) = O(x^{3/2+ε})` per ogni `ε > 0`, allora vale RH; `S(x) = 1 + Σ_{p≤x} p`,
`B(x) = 1 + li(x²) − li(4)`.

## Dizionario
- `S(x)` = `S ⌊x⌋₊` (x reale); `B(x) = 1 + ∫_4^{x²} du/log u` (nota N3).
- `E₁(x) = Σ_{p≤x} p − Li₁(x)`, `Li₁(x) = ∫_2^x t/log t dt` = `LeanBase.Classical.momentError 1 x`.
- RH = `RiemannHypothesis` di Mathlib.

Goal: `(∀ ε > 0, (x ↦ S(x) − B(x)) =O[atTop] (x ↦ x^{3/2+ε})) → RiemannHypothesis`.

## Γ₀
- H1 (lean-base, dimostrato, copia di arcs-algo 372ba68) `prop30_two_imp_RH 1`:
  `(∀ ε > 0 ∃ C ∀ N ≥ 2, E₁(N) ≤ C N^{3/2+ε}) → RiemannHypothesis`.
- H2 cambio di variabile `u = t²`: per `x ≥ 2`, `∫_4^{x²} du/log u = ∫_2^x 2t/log(t²) dt = ∫_2^x t/log t dt`
  (`intervalIntegral.integral_comp_mul_deriv`, `Real.log_pow`).
- H3 `liK 1 x = ∫_2^x t/log t dt` per `x ≥ 2` (definizione di `liK`, integrando nullo su `[0, 2]`).
- H4 `primeRace (powWeight 1) N = Σ_{p≤N} p = S N − 1` (definizioni).
- H5 da `IsBigO` per `x → ∞` a una costante uniforme su `N ≥ 2`: esiste `x₀`, e i naturali in `[2, x₀)`
  sono finiti (massimo su un insieme finito).

## Albero
```
 1. [∀ε>0, S − B = O(x^{3/2+ε})]                          [→I, ipotesi h]
 2. [ε > 0]  ∃ C₀ x₀ ∀ x ≥ x₀, |S(x) − B(x)| ≤ C₀ x^{3/2+ε}   [∀E h, IsBigO_iff, eventually_atTop]
 3. ∀ N ≥ 2: S(N) − B(N) = E₁(N)                          [H2, H3, H4: 1 + Σp − 1 − Li₁(N)]
 4. ∃ C ∀ N ≥ 2: E₁(N) ≤ C N^{3/2+ε}                      [2, 3, H5: C = max(C₀, max_{2≤N<x₀} |E₁(N)|/N^{3/2+ε})]
 5. RiemannHypothesis                                      [→E H1 con 4 (∀I su ε)]
```

## Audit
- R7: H1 è un teorema dimostrato (non un'ipotesi): nessuna ipotesi classica resta. H2–H5: Mathlib e definizioni.
- R8: nessun buco. R9: ε autovariabile di ∀I; C₀, x₀ testimoni di ∃E scaricati in 4.
- R10: FOL classica + analisi di Mathlib; Deps = propext, Classical.choice, Quot.sound.
- Si usa solo la stima superiore `E₁ ≤ C N^{3/2+ε}`: l'ipotesi del paper (con `|·|`) è più forte del necessario.

**Verdetto: CHIUSA**, Γ₀ = {H1, …, H5}; nessuna ipotesi classica.
