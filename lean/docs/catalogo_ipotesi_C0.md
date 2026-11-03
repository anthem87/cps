# Blocco C0 — catalogo delle ipotesi per Lemma A, Teorema 3, Osservazione 1, Teorema 4(a)

Solo enunciati e fonti, niente prove. Ogni ipotesi è una `def Nome : Prop` in `CpsLean/Classical/`,
con fonte, dominio e "An explicit hypothesis, never an axiom." Le definizioni ausiliarie (solo
definizioni) sono in `CpsLean/Zeros.lean` e `CpsLean/LimitDist.lean`.

## Ipotesi (teoremi classici pubblicati)

| Nome Lean | File | Fonte | Usata in |
|---|---|---|---|
| `TruncatedExplicitFormula` | Classical/TruncatedExplicitFormula.lean | Davenport cap. 17 (9)–(10); Strömbergsson Thm 13.2; x ≥ 2, T ≥ 2 | Lemma A, passi 1–3 (con il limite 5/2 di D2) |
| `RiemannVonMangoldt` | Classical/RiemannVonMangoldt.lean | von Mangoldt 1905; Davenport cap. 15 | Lemma A (`Σ|ρ+a|^{−2} < ∞`), Step 5 (`Σ_{T<γ≤T+1} 1 ≪ log T`), Teor. 4(a) (`N′(γ)`) |
| `AnsCor13a` | Classical/AnsCor13a.lean | Akbary–Ng–Shahabi 2014, Thm 1.2 e Cor. 1.3(a) | Step 5 (esistenza di `μ_a`) |
| `AnsThm114` | Classical/AnsThm114.lean | Akbary–Ng–Shahabi, Thm 1.14 (Parseval di Besicovitch) | Step 5 (momenti secondi limitati) |
| `AnsThm19` | Classical/AnsThm19.lean | Akbary–Ng–Shahabi, Thm 1.9 (Kronecker–Weyl), ℓ = 1 | Step 6 (`μ̂_a = e^{−icξ} Π J₀`) |
| `RubinsteinSarnakInversion` | Classical/RubinsteinSarnakInversion.lean | Rubinstein–Sarnak 1994 §3; Gil-Pelaez 1951 | Step 6 (formula di `δ_a`) |
| `BesselDecay` | Classical/BesselDecay.lean | Watson §7.21 | Step 6 (assoluta continuità di `μ_a`) |
| `LindebergFeller` | Classical/LindebergFeller.lean | Lindeberg 1922; Billingsley Thm 27.2 | Teor. 4(a) |
| `Mertens2` | Classical/Mertens.lean | Mertens 1874; Hardy–Wright Thm 427 | Osservazione 1 |

## Congettura (solo antecedente)

| Nome Lean | File | Fonte | Usata in |
|---|---|---|---|
| `LI` | Classical/LI.lean | Wintner 1935; Rubinstein–Sarnak §1 | Teor. 3(ii), Teor. 4 |

`RiemannHypothesis` è quella di Mathlib.

## Scelte di forma (nessuna rende l'enunciato più forte di quello pubblicato)

1. **ANS, frequenze.** ANS ammettono `λ_n` non decrescenti; qui strettamente crescenti (frequenze
   uguali raggruppate, coefficienti sommati). La formula del Thm 1.14 così come è stampata vale
   solo con `λ_n` distinti; per gli zeri di ζ si raggruppano le ordinate uguali (molteplicità).
2. **ANS, (1.6)–(1.7).** L'errore `E(y, X)` è definito come differenza, quindi (1.6) è automatica
   e (1.7) diventa una condizione su `φ, c, λ, r`. In più si chiede `φ` misurabile e di quadrato
   integrabile su ogni `[0, Y]` (ANS lo usano senza dirlo).
3. **ANS, (1.11).** `Σ_{T<λ_n≤T+1} 1 ≪ log T` è chiesta per T grande (`∀ᶠ T in atTop`): per T vicino
   a 1 il `log T` si annulla, quindi la lettura "per ogni T > 0" sarebbe falsa.
4. **ANS, J₀.** `AnsThm19` usa il `J₀` di ANS, `∫_0^1 e^{−iz cos 2πt} dt` (`ansJ0`); il resto del
   progetto usa la serie (`besselJ0`). L'uguaglianza è da dimostrare (vedi sotto).
5. **ANS, media.** "lim (1/Y)∫φ = c" ANS lo dicono solo di passaggio; il paper lo dimostra
   (Step 5): non è un'ipotesi, è da dimostrare.
6. **Formula troncata.** Scritta come in Davenport (ψ₀, `|γ| < T`, `−ζ′(0)/ζ(0)`, `⟨x⟩`), dominio
   x ≥ 2, T ≥ 2 come in Strömbergsson. **G3 resta aperto:** pagina e dominio da verificare sul
   Davenport cartaceo.
7. **LI** con molteplicità: zeri con γ > 0 semplici, ordinate distinte per zeri distinti, ordinate
   linearmente indipendenti su ℚ.
8. **Mertens:** forma di Hardy–Wright (con la costante e `O(1/log x)`); il paper usa solo `+ O(1)`.

## Foglie da dimostrare (non ipotesi)

- `Σ_ρ |ρ + a|^{−2} < ∞` e `Σ_{T<γ≤T+1} 1 ≪ log T`, da `RiemannVonMangoldt`.
- `ansJ0 = besselJ0` (integrazione termine a termine) e `E[e^{iξρ cos U}] = J₀(ρξ)`.
- La media di `μ_a` (Step 5: momenti secondi uniformi ⇒ convergenza dei primi momenti, media di
  `e^{iγy}` nulla).
- Pólya (convergenza uniforme delle ripartizioni verso un limite continuo).
- L'estensione di Lindeberg dalla somma finita alla serie `Σ_γ ρ_γ cos U_γ` (troncamento).

## Note per formalization.yaml

Le voci `classical theorem` si aggiungono quando un teorema confrontato le usa (oggi nessuno: il
Challenge non cambia). Nota prevista: "Explicit hypothesis `X` of Theorem 3 (…); not formalized".
