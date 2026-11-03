# Divergenze tra il paper e gli enunciati Lean

Paper: A. Mennillo, *Cumulative Prime Sums and Riemann Zeros: a fine grid, its ripple, and a family
of prime races*, versione 3, Zenodo, DOI 10.5281/zenodo.23269807.

Per ogni enunciato che in Lean differisce dal paper: enunciato del paper e enunciato Lean affiancati,
motivo e decisione dell'autore. In fondo: note Lean (nessuna differenza di enunciato) e punti del paper
da precisare nella v4.

## 1. Divergenze di enunciato

### D1 — Proposizione 1 (precisazione fedele alla prova del paper)

| Paper | Lean |
|---|---|
| Def. 2: per `t ≥ log 3`, `N(t) = min{p primo : log S_p ≥ t}`. **Prop. 1.** *`N(t)` è primo per ogni `t`.* Prova: "`S_N` cambia solo quando `N` è primo, quindi il primo `N` in cui `log S_N` supera `t` è primo." | `CPS.prop1_crossing_prime`: per ogni `t ≥ log 3`, `N(t) = min{N ≥ 1 : t ≤ log S_N}` e `N(t)` è primo. |

Motivo. Con la Def. 2 letta alla lettera (minimo sui primi) la Prop. 1 è tautologica; la prova del
paper ragiona sul minimo su **tutti** gli `N`. Quella versione vale nel dominio della Def. 2 (`t ≥ log 3`;
in realtà per ogni `t > 0`) ma non per `t ≤ 0`, dove il minimo è `N = 1`. L'enunciato Lean prende la
lettura della prova, nel dominio della Def. 2. Decisione dell'autore: 3 novembre 2026.

### D2 — Lemma A, passi 1–3 (riparazione di G3) — *per il Blocco C, non ancora in Lean*

| Paper | Lean (previsto) |
|---|---|
| Passo 1: `Π_a(x) = ∫_{3/2}^x t^a/log t dψ(t)`, e la formula esplicita troncata (Davenport cap. 17) "per `t ≥ 3/2` e `T ≥ 2`", usata a `t = 3/2` (passo 2) e su `[3/2, x]` (passo 3). | `Π_a(x) = 2^a + ∫_{5/2}^x t^a/log t dψ(t)` per `x ≥ 5/2` (il salto di `ψ` in `2` dà il termine `2^a`); la formula troncata si usa solo per `t ≥ 2`, dominio in cui è enunciata; `⟨5/2⟩ = 1/2`. Il termine `2^a` è `O(1)` e finisce nel resto. |

Motivo. La formula troncata con il resto `x log²(xT)/T + log x · min(1, x/(T⟨x⟩))` è enunciata per
`x ≥ 2`, `T ≥ 2` (A. Strömbergsson, *Analytic Number Theory — Lecture notes based on Davenport's book*,
Uppsala 2008, Teorema 13.2, §13 = Davenport cap. 17; la forma esatta, Teorema 13.1, vale per `x > 1`).
[VERIFICARE SUL VOLUME: Davenport, *Multiplicative Number Theory*, 3ª ed., GTM 74, cap. 17, pp. 104–110.]
Decisione dell'autore: 3 novembre 2026.

### D3 — Step 2 del Teorema 3 — *per il Blocco B, non ancora in Lean*

| Paper | Lean (previsto) |
|---|---|
| `½θ_{2a}(√x) = x^{a+1/2}/((2a+1) log x)·(1 + O(1/log x))`, ottenuto "dal PNT per il peso `t^{2a}`" con `(1 + o(1))`. | Lo stesso enunciato incorniciato, `1 + O(1/log x)`, ricavato dall'ipotesi `VonKochPsi` (RH ⇒ `ψ(x) = x + O(√x log² x)`), già necessaria per la Prop. 3(a). |

Motivo. Con il solo PNT si ottiene `1 + o(1)`, non `1 + O(1/log x)` (G1 dell'audit). L'enunciato del
paper resta invariato; cambia la fonte del termine d'errore. Decisione dell'autore: 3 novembre 2026.

## 2. Note Lean (nessuna differenza di enunciato)

- **N1 — Teorema 2, `S_{p_m} ≥ 2p_m > p_{m+1}` (G5).** Il paper usa il postulato di Bertrand nella
  forma classica (Chebyshev), stretta: `n < p < 2n` per `n > 1`. Mathlib ha la forma
  `Nat.exists_prime_lt_and_le_two_mul` (`n < p ≤ 2n`); la disuguaglianza stretta si ottiene in Lean
  aggiungendo che `2n` non è primo per `n ≥ 2`. Non è un difetto del paper.
- **N2 — Indici.** In `CpsLean` `p_m` ha gli indici del paper (`p₁ = 2`); il lemma
  `CPS.prime_eq_leanBase` lo collega a `LeanBase.PrimeSums.p (m − 1)` (dove `p 0 = 2`).
- **N3 — `B(x) = 1 + li(x²) − li(4)`.** In Lean `li(x²) − li(4)` è scritto `∫_4^{x²} du/log u`: è la
  stessa quantità (per `1 < a ≤ b`, `li(b) − li(a) = ∫_a^b du/log u`) senza il valore principale in `0`.
- **N4 — Prop. 3(b).** L'ipotesi del paper è `S(x) − B(x) = O(x^{3/2+ε})` per ogni `ε > 0`, con `x` reale
  (`S(x) = 1 + Σ_{p≤x} p`); in Lean è scritta con `Asymptotics.IsBigO` per `x → ∞` reale, come nel paper.
  La prova usa solo la stima superiore sui naturali (Landau, `LeanBase.Classical.prop30_two_imp_RH 1`).
- **N6 — Lemma J.** Lemma di libreria, fuori dal confronto, per il futuro Teorema 4(b): non è un
  enunciato del paper (è il lemma ausiliario proposto dall'audit). È in `CpsLean/Bessel`
  (`CpsLean.lemmaJ`, `0 ≤ J₀(x) ≤ e^{−x²/4}` per `|x| ≤ 2`), con il controllo assiomi, ma non in
  Challenge.lean. Entra nel confronto solo se il Teorema 4(b) viene promosso nel paper.
- **N5 — Teorema 2, parte asintotica.** `δ(t) = (1+o(1))√t e^{−t/2}` è il Teorema 1(ii) (il paper:
  "The asymptotics is Theorem 1"); entra nel Blocco B con l'ipotesi PNT. Il Blocco A contiene tutto il
  resto del Teorema 2.

## 3. Formulazioni informali, da precisare nella v4 (non si formalizzano)

- **§8.1, formula del ripple.** `f(u) = −1/3 − 2 Re Σ_{γ>0} e^{iγu}/(3/2 + iγ) + O(1/u)` è scritta con la
  somma non troncata, che non converge assolutamente. La forma rigorosa è quella dello Step 4 del
  Teorema 3 con `a = 1`: troncamento `0 < γ ≤ T`, `T = e^Y ≥ x`, errore `≪ 1/y + Y²e^{−Y/2}`.
- **§8.3, due scale.** "il ripple `|log S − log B| ≍ e^{−t/4}`" e "se gli zeri avessero parte reale fino a
  `Θ > ½`, il ripple sarebbe dell'ordine `e^{−(1−Θ)t/2}`": il paper dimostra solo la stima superiore
  (Prop. 3(a)); la stima inferiore (`≍`) richiede un Ω-teorema che il paper non dà.
