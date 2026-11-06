# Divergenze tra il paper e gli enunciati Lean

Paper: A. Mennillo, *Cumulative Prime Sums and Riemann Zeros: a fine grid, its ripple, and a family
of prime races*, versione 4, Zenodo, novembre 2026, DOI 10.5281/zenodo.23962478.

Le voci sono state scritte sulla versione 3 (DOI 10.5281/zenodo.23269807): la colonna "Paper" riporta il testo
della v3. L'Appendice B della v4 elenca le correzioni che la v4 ha recepito.

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

### D2 — Lemma A, passi 1–3 (dominio della formula troncata, G3)

| Paper | Lean |
|---|---|
| Passo 1: `Π_a(x) = ∫_{3/2}^x t^a/log t dψ(t)`, e la formula esplicita troncata (Davenport cap. 17) "per `t ≥ 3/2` e `T ≥ 2`", usata a `t = 3/2` (passo 2) e su `[3/2, x]` (passo 3). | `Π_a(x) = 2^a + ∫_{5/2}^x t^a/log t dψ(t)` per `x ≥ 5/2` (il salto di `ψ` in `2` dà il termine `2^a`); la formula troncata si usa solo per `t ≥ 2`, dominio in cui è enunciata; `⟨5/2⟩ = 1/2`. Il termine `2^a` è `O(1)` e finisce nel resto. |

Motivo. La fonte consultata allora (A. Strömbergsson, *Analytic Number Theory — Lecture notes based on Davenport's book*,
Uppsala 2008, Teorema 13.2) enuncia la formula troncata per `x ≥ 2`, `T ≥ 2`. Fonte primaria: H. L. Montgomery, R. C. Vaughan,
*Multiplicative Number Theory I*, CUP 2007, Teorema 12.5, p. 400: per `c > 1` fissato, `x ≥ c`, `T ≥ 2`, somma su `|γ| ≤ T`,
`R ≪_c log x · min(1, x/(T⟨x⟩)) + (x/T) log²(xT)`. La forma Lean (`x ≥ 2`, `|γ| < T`) ne segue: gli zeri con `|γ| = T` sono
`≪ log T` e contribuiscono `≪ x log T / T`. Con `c = 3/2` il teorema copre anche l'uso del paper su `t ≥ 3/2`; il Lean resta su `x ≥ 2`.
Decisione dell'autore: 3 novembre 2026.

### D3 — Step 2 del Teorema 3

| Paper | Lean |
|---|---|
| `½θ_{2a}(√x) = x^{a+1/2}/((2a+1) log x)·(1 + O(1/log x))`, ottenuto "dal PNT per il peso `t^{2a}`" con `(1 + o(1))`. | `CPS.step2_bias_layer`: sotto `VonKochPsi` e RH, per ogni reale `a > −½`, `(x ↦ ½θ_{2a}(√x) − M(x)) = O(M(x)/log x)` con `M(x) = x^{a+1/2}/((2a+1) log x)`: lo stesso enunciato incorniciato. |

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
- **N7 — Ipotesi classiche del Blocco B.** `PNT` (`π(x) ∼ x/log x`) per Teorema 1, parte
  asintotica del Teorema 2, Proposizione 2 e Corollario 2 (`CpsLean/Classical/PNT.lean`); `VonKochPsi`
  (sotto RH, `ψ(x) = x + O(√x log² x)`; in `lean-base/LeanBase/Hypotheses.lean`, accanto a `VonKochPi`,
  la forma con `π` usata da ARCS)
  per la Proposizione 3(a) e lo Step 2. Sono i teoremi che il paper usa; RH compare solo come
  antecedente. Le conseguenze del PNT usate nella prova del Teorema 1 (`Σ_{p≤x} p ∼ x²/(2 log x)`,
  `p_{m+1}/p_m → 1`) e l'ipotesi `PNTcons` di lean-base sono dimostrate da `PNT`.
  Step 2 del Teorema 3: la formula incorniciata vale incondizionatamente con l'errore di de la
  Vallée Poussin (`θ_b(y) = ∫ t^b/log t + O(y^{b+1} e^{−c√log y})`); il Lean la dimostra sotto RH
  (via `VonKochPsi`), il che basta per il Teorema 3, che è condizionale a RH (vedi D3).
- **N8 — Corollario 2, quantificatori.** `o(1)` per `t → ∞`, uniforme in `t′ ≥ t`: per ogni `ε > 0`
  esiste `T` con `|N(t′)/N(t) / (e^{(t′−t)/2}√(t′/t)) − 1| < ε` per `T ≤ t ≤ t′`. Il paper non fissa i
  quantificatori.
- **N9 — Teorema 1(i), "∼".** `Δ_m ∼ 2/m` è `Asymptotics.IsEquivalent` per `m → ∞`; lo stesso per
  `δ(t) = (1+o(1))√t e^{−t/2}` (Teorema 1(ii)) e `N(t) = (1+o(1))√t e^{t/2}` (Corollario 2).
- **N10 — Ipotesi del Blocco C (catalogo C0).** Elenco, fonti e scelte di forma in
  `lean/docs/catalogo_ipotesi_C0.md`. Nessuna è più forte del teorema pubblicato. Le differenze di
  forma: frequenze di Akbary–Ng–Shahabi strettamente crescenti; la condizione `Σ_{T<λ_n≤T+1} 1 ≪ log T`
  per T grande; `φ` misurabile e localmente L²; LI con molteplicità.
- **N11 — Blocco C, Lemma A.** Enunciato come nel paper: `CPS.lemmaA`. `Π_a` è scritto `Σ_{n≤x} n^a Λ(n)/log n`
  (`Λ(p^k)/log(p^k) = 1/k`); l'identità `Π_a = θ_a + ½θ_{2a}(√x) + R` è dimostrata (`piA_eq_layers`). `li` è il valore
  principale; la sua esistenza è dimostrata (`tendsto_li`). La somma su `|γ| ≤ T` conta le molteplicità. Prova:
  D2 (formula troncata solo per `t ≥ 5/2`); la formula ha `|γ| < T`, il passaggio a `|γ| ≤ T` è nel termine d'errore.
- **N12 — Blocco C, Step 3 (G2).** Stessa conclusione del paper: `CPS.step3_layers`, `R = o(x^{a+½}/log x)`, e nella
  libreria `R ≤ C x^{a+½}/log²x` (`layersR_le`). La prova non separa i valori di transizione `ka ≈ −1`: un esponente
  uniforme `b′ = min(k|a|, 1−δ)` copre tutti i `k`. G2 è quindi assorbita, non riscritta (derivazione in
  `lean/docs/noescape/Step3_Layers.md`).
- **N13 — Blocco C, Step 4.** `CPS.step4_assembling`, per `log 3 ≤ y ≤ Y`, con le molteplicità. Serve che nessuno zero
  abbia `γ = 0`: `ζ(σ) ≠ 0` su `(0, 1)` non è in Mathlib ed è dimostrato (`riemannZeta_ne_zero_of_real`, serie alternante).
- **N14 — Blocco C, Teorema 3(i).** `CPS.theorem3_i`. Il paper definisce `E_a(x)` per `x ≥ 2`: `φ(y) = E_a(e^y)` per
  `y ≥ log 2`, `0` prima (non cambia la distribuzione limite). Con le molteplicità i coefficienti sono
  `r_n = −2 m_n/(½+a+iλ_n)` a ordinate distinte, quindi `β = ¾` invece di `β = 1` (basta `β > ½`). La media
  `−1/(2a+1)` è dimostrata (`mean_of_limiting`, `mean_phiA`): la convergenza `(1/Y)∫φ → c` viene direttamente dallo
  Step 4, senza la seminorma `B²` del paper; `AnsThm114` serve solo per i momenti secondi.
- **N15 — Blocco D, Teorema 3(ii).** `CPS.theorem3_ii`, per ogni distribuzione limite `μ` di `E_a(e^y)`. La densità logaritmica è
  `(1/log X) ∫_2^X 1_S(x) dx/x → d` (`HasLogDensity`). `∏'` e `∫` sono accompagnati da due congiunti in più (prodotto moltiplicabile,
  integrando integrabile), che escludono i valori di comodo: l'enunciato è più forte, non diverso. Il prodotto è sulle ordinate distinte;
  sotto LI gli zeri sono semplici. Prova: `μ_a` come legge di `X_a` con `U_γ` i.i.d. non serve, basta `AnsThm19`; `ansJ0 = besselJ0` è
  dimostrata. L'assoluta continuità, che il paper deduce dall'integrabilità di `μ̂_a` (Mathlib non ha l'inversione per misure), passa
  per `RubinsteinSarnakInversion`, già tra le ipotesi: `ν(u, v] ≤ M(v − u)` con `M = (1/π)∫_0^∞|ν̂|`. Il decadimento è dimostrato da
  `BesselDecay` per ogni `N` (`abs_prodJ_le_pow`). L'ultima frase dell'enunciato ("For `a = 0` this is the classical bias `−1` and the
  density `2.6·10⁻⁷`"): il bias `−1` è il caso `a = 0` della formula; il valore numerico non è formalizzato.
- **N16 — Blocco D, Teorema 4(a).** Il paper cita Lindeberg; il Lean dimostra la convergenza delle funzioni caratteristiche
  `Π J₀(ρ_γ ξ/σ_a) → e^{−ξ²/2}` e conclude con la continuità di Lévy di Mathlib. Stesso contenuto, un'ipotesi in meno. La stima usata è
  `|J₀(x) − e^{−x²/4}| ≤ x⁴/8` per ogni `x` (con il Lemma J per `|x| ≤ 2`), con somma telescopica sui fattori: non servono né `log J₀` né
  la positività. Pólya è sostituito dal sandwich `(ν/σ)(ε, ∞) ≤ δ_a ≤ ½`, che dimostra la parte necessaria. La varianza,
  `σ_a² ∼ log(A/2π)/(2A)`, è `CPS.theorem4a_variance`: sommazione di Abel con `RiemannVonMangoldt`, senza usare il valore di
  `∫_0^∞ u² log u/(1+u²)² du` (basta che sia finito).
- **N17 — Blocco D, Osservazione 1.** `CPS.remark1_deterministic` (tre affermazioni su `B_a`, senza ipotesi) e `CPS.remark1_mertens`
  (`Mertens2`). Lo "Status" del paper, sul termine degli zeri a `a = −½`, resta "at the level of a remark" e non si formalizza.
- **N18 — Blocco E, Teorema 4(b).** Il paper lo enuncia come "Heuristic, with numerical support"; il Lean lo dimostra sotto RH ∧ LI
  (`CPS.theorem4_b`): `½ − δ_a ∼ b_a/(σ_a√(2π))` e `½ − δ_a ∼ 1/(2√(πA log(A/2π)))`. L'enunciato è quello del paper; cambia lo statuto.
  Il testo del paper non si tocca. Ipotesi: RH, LI, `RiemannVonMangoldt`, `BesselDecay`; la prova usa la formula di `δ_a`, non `μ_a`.
  Il legame con la densità logaritmica è il Teorema 3(ii). Prova: `W = (X_a − b′)/σ_a` con lo shift `b′ = −1/(2A)`; `θ = sup_{|u|≥√2}|J₀(u)| < 1`
  senza valore numerico (`exists_theta`); Lemma W, con taglio in `|ξ| = A` (`lemmaW`, `lemmaW_uniform`); `½ − δ_a = P(0 < W ≤ h_a)`
  (`half_sub_deltaA_eq`). Nella conclusione il Lean passa da `½ − δ_a = (h_a/π)∫_0^∞ sinc(h_a s) P_a(s/σ_a) ds`, cioè dalla forma
  integrata della densità `f_a`: stesso contenuto, senza Fubini e senza riconoscere `f_a` come densità di `W`. Per il conteggio degli zeri
  si usa `K = ⌊A⌋ ≤ #{0 < γ ≤ A}`. Nessuna ipotesi nuova rispetto al catalogo. Lemma W e `half_sub_deltaA_eq` non sono enunciati del
  paper: stanno in libreria, fuori dal confronto (come il Lemma J). `CPS.theorem4_b_density` è il Teorema 4(b) sulla densità logaritmica della
  gara, con le ipotesi di `theorem3_ii` e `AnsCor13a`: `theorem3_ii` più `theorem4_b`; `CPS.theorem4_b` ne è la forma analitica su `deltaA`.
- **N19 — Numerici.** `CPS.grid_integers`, `CPS.table1_primes`, `CPS.first_crossing_table`, `CPS.first_crossing_a1` sono dimostrati nel kernel con
  `decide +kernel` (nessun assioma in più, niente `native_decide`). `CPS.table1_crossing` ha come ipotesi il certificato `Table1Cert`; la primalità
  di `N_n` è dimostrata e quindi non sta nel certificato. `S(N_n)` per `n ≥ 2` resta nel certificato: non si calcola nel kernel.
  `CPS.first_crossing_a1` vale su `x ≥ 2`: per `x` appena sopra `1`, `li(x²) < 0 = θ₁(x)`, e il paper definisce `E_a` per `x ≥ 2`.
- **N6 — Lemma J.** Lemma di libreria, fuori dal confronto: non è un enunciato del paper (è il lemma ausiliario proposto dall'audit).
  È in `CpsLean/Bessel` (`CpsLean.lemmaJ`, `0 ≤ J₀(x) ≤ e^{−x²/4}` per `|x| ≤ 2`), con il controllo assiomi, ma non in `lean/MainTheorems.lean`.
  È usato da `abs_besselJ0_sub_exp_le` (Teorema 4(a)) e da `prodJ_central` (Lemma W, Teorema 4(b)).
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
