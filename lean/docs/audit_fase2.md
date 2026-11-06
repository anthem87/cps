Superato per T4b da N18 (Blocco E)

# CPS v3 — audit di fase 2 (3 novembre 2026)

Fonte di verità: CPS v3, Zenodo DOI 10.5281/zenodo.23269807; sorgente `cps_v3.tex` (testo uguale al PDF
pubblicato). Base: `prism-polya/release/NEXT/dal_progetto/CPS_NoEscape_2026-11-03.md` ("l'audit"),
verificato enunciato per enunciato contro il tex. Mathlib: rev 3e18214 (cartella condivisa).

Classi: (i) dimostrabile con Mathlib (+ lean-base); (ii) teorema classico → ipotesi `def … : Prop`;
(iii) certificato numerico → ipotesi con script; (iv) euristica/numerico/testo, non formalizzabile.
Difficoltà: ★ facile … ★★★★★ molto pesante.

## 1. Inventario

Notazione del paper: `p_m` m-esimo primo (`p₁ = 2`), `S_N = 1 + Σ_{p≤N} p`, `σ_m = log S_{p_m}`,
`Δ_m = σ_{m+1} − σ_m`, `m(t)` con `σ_{m(t)−1} < t ≤ σ_{m(t)}`, `δ(t) = Δ_{m(t)−1}`.

| # | Paper | Enunciato (sintesi fedele) | Dipende da | Classe | Diff. |
|---|---|---|---|---|---|
| D1 | Def. 1 | `S_N`, `σ_m`; `(σ_m)` strettamente crescente, `σ₁ = log 3` | — | (i) | ★ |
| D2 | Def. 2 | `N(t) = min{p primo : log S_p ≥ t}`, `ε(t) = log S_{N(t)} − t ≥ 0`, per `t ≥ log 3` | D1 | (i) | ★ |
| D3 | §3 | `Δ_m = log(1 + p_{m+1}/S_{p_m})`, `m(t)`, `δ(t)` (per `t > log 3`) | D1 | (i) | ★ |
| P1 | Prop. 1 | `N(t)` è primo per ogni `t` | D2 | (i) | ★ |
| T1 | Teor. 1 | (i) `Δ_m ∼ 2/m`; (ii) `δ(t) = (1+o(1))√t e^{−t/2}` | D3, PNT | (ii) | ★★★ |
| T2 | Teor. 2 | `S_{p_m} ≥ p_{m+1}` ∀m≥1; `Δ_m ≤ log 2`, `=` solo per m=1; `ε(log 3) = 0`; ∀t>log 3: `0 ≤ ε(t) < δ(t) ≤ log 2`; `δ(t) = (1+o(1))√t e^{−t/2}` | D2, D3, Bertrand; T1(ii) per l'ultima parte | (i) + (ii) per l'asintotica | ★★ |
| RB | Oss. (Brown) | ogni intero in `[1, S_{p_m}]` è somma di elementi distinti di `{1,2,3,5,…,p_m}` | T2 | (i) | ★ |
| C1 | Cor. 1 | principio di genericità (riformulazione di T2 per ogni t) | T2 | (iv) testo; il contenuto è T2 | — |
| RU | §4 | dentro una cella `U` è lineare in t; t uniforme sulla cella ⇒ U uniforme su [0,1) | D3 | (i) opzionale | ★★ |
| RI | §4 | griglia degli interi: `τ_{N+1} − τ_N = log(1+2/N)`, equivalente `√2 e^{−τ_N/2}` | — | (i) opzionale | ★ |
| RW | §4 | pesi `p^a`: cella di ordine `t^{a/(a+1)}e^{−t/(a+1)}` | PNT pesato | (iv) (solo "by the argument of Theorem 1") | — |
| P2 | Prop. 2 | `t = 2 log N − log log N − log 2 + o(1)` lungo `N = N(t)` | T1, PNT | (ii) | ★★★ |
| C2 | Cor. 2 | `N(t) = (1+o(1))√t e^{t/2}`; `N(t′)/N(t) = e^{(t′−t)/2}√(t′/t)(1+o(1))` | T1, P2 | (ii) | ★★ |
| — | §6 | approssimazione garantita (= T2), somme esatte, semi per Newton, tabella di Newton | — | (iv) / (iii) | — |
| RD | Oss. (operatore diagonale) | `Ĥ` autoaggiunto, spettro discreto semplice; `dist(t, {σ_m}) → 0` | T2 | (i) solo la parte `dist → 0`; l'autoaggiunzione illimitata è pesante | ★/★★★★ |
| Q | §7 | domanda della griglia; protocollo e test | — | (iv) | — |
| F8 | §8.1 | `f(u) = −1/3 − 2Re Σ_{γ>0} e^{iγu}/(3/2+iγ) + O(1/u)` sotto RH | Teor. 3 Step 4 (a=1) | (ii) | ★★★★ |
| — | §8.2 | spettro del ripple, Tabelle 2–3 | — | (iv) | — |
| P3a | Prop. 3(a) | RH ⇒ `S(x) − B(x) = O(x^{3/2} log x)` e `|log S − log B| = O(log²x/√x)` | RH, von Koch (forma ψ), ψ−ϑ | (ii) | ★★★ |
| P3b | Prop. 3(b) | `S − B = O(x^{3/2+ε})` ∀ε ⇒ RH | Landau | **(i): già dimostrata in arcs-algo** (vedi §3) | ★ (riuso) |
| S2 | §8.3 | due scale: ripple `≍ e^{−t/4}`; se Θ > ½ il ripple è `≍ e^{−(1−Θ)t/2}` | P3 + un Ω-teorema | (iv): il paper non lo dimostra (vedi A10) | — |
| X109 | §9.1 | `Σ_{p≤x} p` supera `li(x²)` per la prima volta a x = 109 | — | (iii) | ★★ |
| NT | §9.2 | `Π_a = Σ_k θ_{ka}(x^{1/k})/k`; `li(x^{a+1}) = PV∫_0^x t^a dt/log t` | — | (i) | ★★ |
| LA | Lemma A | RH, `Y ≥ 2`, `T = e^Y`, `3 ≤ x ≤ e^Y`: `Π_a(x) = li(x^{a+1}) − (x^κ/log x)Σ_{|γ|≤T} x^{iγ}/(ρ+a) + O_a(…)` | RH, formula esplicita troncata, `Σ|ρ+a|^{−2} < ∞` | (ii) | ★★★★★ |
| ST2 | Teor. 3 Step 2 | `½θ_{2a}(√x) = x^{a+1/2}/((2a+1)log x)·(1 + O(1/log x))` | PNT pesato (G1) | (ii) | ★★★ |
| ST3 | Teor. 3 Step 3 | `Σ_{k≥3} θ_{ka}(x^{1/k})/k = o(x^{a+1/2}/log x)` | Chebyshev (Mathlib), somma `Σ p^{−s}`, s>1 (Mathlib) | (i) | ★★ (a ≥ 0) / ★★★ (a < 0) |
| T3i | Teor. 3(i) | RH ⇒ `E_a` ha distribuzione logaritmica limite `μ_a` con media `−1/(2a+1)` | LA, ST2, ST3, ANS Thm 1.2/Cor 1.3(a), Thm 1.14, Besicovitch, RvM locale | (ii) | ★★★★★ |
| T3ii | Teor. 3(ii) | RH+LI ⇒ `μ_a` ass. continua, simmetrica; `δ_a = ½ − (1/π)∫ sin(ξ/(2a+1))/ξ · Π J₀(…) dξ` | T3i, LI, ANS Thm 1.9, asintotica di J₀, inversione R–S | (ii) | ★★★★★ |
| R1 | Oss. 1 | `B_{−1/2}(x) = ½(log log √x − log log 2)`; Mertens: `½Σ_{p≤√x} 1/p = ½ log log x + O(1)` | Mertens | (i) l'integrale; (ii) Mertens | ★ / ★★ |
| T4a | Teor. 4(a) | RH+LI ⇒ `δ_a → ½` per a → ∞ (con `σ_a² ∼ log(A/2π)/(2A)`) | T3ii, RvM, Lindeberg, Pólya | (ii) | ★★★★ |
| T4b | Teor. 4(b) | euristica (dichiarata) | — | (iv): **non si promuove**; solo il Lemma J | — |
| LJ | audit §3 | Lemma J: `|x| ≤ 2 ⇒ 0 ≤ J₀(x) ≤ e^{−x²/4}` | definizione di J₀ come serie | (i) | ★★ |
| — | Tab. 1, 4–6, Fig. | valori numerici | — | (iii)/(iv) | — |

## 2. Ordine topologico

D1 → D2, D3 → P1, T2(elementare), RB, RU, RD(dist) → [PNT] T1(i) → T1(ii) → T2(asintotica), C2, P2.
NT, ST3, R1(integrale), LJ: indipendenti. [Landau] P3b. [RH, von Koch] P3a.
[RH, formula esplicita] LA → [PNT pesato] ST2 → Step 4 → [ANS] T3i → [LI, ANS] T3ii → [Lindeberg] T4a.
Nessun ciclo (conferma §2 dell'audit: T2 usa T1 solo per l'asintotica di δ).

## 3. Foglie: Mathlib (rev 3e18214), lean-base, ipotesi, da dimostrare

| Foglia | Stato |
|---|---|
| `Nat.nth Nat.Prime`, `Nat.prime_nth_prime`, `Nat.nth_prime_zero_eq_two`, `Nat.nth_strictMono`, `Nat.le_nth_of_lt_nth_succ`, `Nat.nth_count` | in Mathlib |
| Bertrand `Nat.exists_prime_lt_and_le_two_mul` (forma `n < p ≤ 2n`) | in Mathlib |
| `p_succ_lt` (`p_{m+1} < 2p_m`), `r_lt_one`, `S_succ`, `grid_step` (Δ esatto), `p_le_sum` | in lean-base (`LeanBase.PrimeSums`, indice `p 0 = 2`) |
| `S_{p_m} ≥ 2p_m` per m ≥ 2 (la forma del paper; lean-base ha solo `2p_m ≤ 1 + S`) | da dimostrare ★ |
| Brown (`brown_mpr`, `IsSubsetSum`) | in lean-base (`LeanBase.SubsetSum`) |
| PNT (`π(x) ∼ x/log x` o `θ(x) ∼ x`) | **non in Mathlib** (solo Chebyshev) → ipotesi `PNT` |
| Conseguenze `p_{m+1}/p_m → 1`, `S_{p_m}/(m p_m) → ½` e `m·Δ_m → 2` | in lean-base come `PNTcons` (ipotesi) + `r_asymp` (dimostrato); oppure da dimostrare da `PNT` ★★★ |
| Chebyshev: `Chebyshev.theta_le_log4_mul_x`, `theta_ge`, `pi_le_log4_mul_div`, `pi_ge`, `primeCounting_eq_theta_div_log_add_integral` | in Mathlib |
| `ψ − θ = O(√x)`: `Chebyshev.isBigO_psi_sub_theta_sqrt`, `abs_psi_sub_theta_le_sqrt_mul_log` | in Mathlib |
| Abel / sommazione parziale: `sum_mul_eq_sub_integral_mul` (`Mathlib.NumberTheory.AbelSummation`) | in Mathlib |
| Integrale di Stieltjes: `StieltjesFunction` e la sua misura (nessun ∫ f dg dedicato) | in Mathlib (parziale); per Step 1 si passa ad Abel |
| `li`, integrale logaritmico | **non in Mathlib**; `liK k` (k ∈ ℕ) in lean-base; per a reale serve `∫_2^x t^a/log t` da definire ★ |
| `Σ_p p^{−s}` convergente per s > 1: `Nat.Primes.summable_rpow` | in Mathlib |
| Mertens (`Σ_{p≤x} 1/p = log log x + O(1)`) | **non in Mathlib** (solo divergenza) → ipotesi `Mertens2` |
| `RiemannHypothesis` | in Mathlib (`Mathlib.NumberTheory.LSeries.RiemannZeta`) |
| Landau: bound unilaterale sui momenti ⇒ RH | **dimostrato in arcs-algo**: `ArcsAlgo.Classical.prop30_two_imp_RH k` (k=1 è P3b) |
| von Koch, forma ψ: RH ⇒ `ψ(x) = x + O(√x log²x)` | ipotesi `VonKochPsi` (arcs-algo ha `VonKoch` in forma π, non basta per `x^{3/2} log x`) |
| zeri di ζ: `riemannZetaZeros` (discreto, chiuso) | in Mathlib; molteplicità e somma su `|γ| ≤ T` da costruire ★★★ |
| formula esplicita troncata (Davenport cap. 17) | ipotesi `TruncatedExplicitFormula` (x ≥ 2, T ≥ 2: vedi G3) |
| `N(T+1) − N(T) ≪ log T`, `N′(γ) ∼ (1/2π)log(γ/2π)`, `Σ|ρ|^{−2} < ∞` (Riemann–von Mangoldt) | ipotesi `RiemannVonMangoldt` |
| ANS Thm 1.2/Cor 1.3(a), Thm 1.9 (Kronecker–Weyl), Thm 1.14; media di Besicovitch | ipotesi (una per teorema) |
| LI (ordinate con molteplicità, G4) | ipotesi-antecedente `LI` |
| Bessel J₀ | **non in Mathlib** → definizione come serie `Σ (−1)^k (x/2)^{2k}/(k!)²`; asintotica `|J₀(x)| ≪ x^{−1/2}` ipotesi |
| inversione di Rubinstein–Sarnak (§3) | ipotesi, o da dimostrare con `charFun` di Mathlib ★★★★ |
| TLC di Lindeberg | **non in Mathlib** (solo i.i.d.: `tendstoInDistribution_inv_sqrt_mul_sum`) → ipotesi `Lindeberg` |
| convergenza debole: `TendstoInDistribution`, `ProbabilityMeasure.tendsto_iff_tendsto_charFun` | in Mathlib |
| Pólya (convergenza uniforme delle ripartizioni a limite continuo) | da dimostrare ★★ |
| `S(4691) = 1 378 036`, `N₁ = 4691` | calcolo nel kernel senza `native_decide`: da verificare se fattibile ★★ |
| `γ_n`, `li(109²)` e tabelle | certificati (iii) |

## 4. Disaccordi con l'audit del 3 novembre

| ID | Punto | Audit | Esito della verifica |
|---|---|---|---|
| A1 | G5, Teor. 2 | il paper usa "2p_m non primo" senza dirlo | Non è un buco del paper: il postulato di Bertrand classico (Chebyshev) è stretto, `n < p < 2n`. È solo un passo in più in Lean, perché Mathlib ha `p ≤ 2n`. |
| A2 | Teor. 2 | goal G1–G4 | Manca `ε(log 3) = 0`, che è nell'enunciato. Banale (`σ₁ = log 3`), ma va nell'enunciato Lean. |
| A3 | Prop. 1 | "CHIUSA" | Con la Def. 2 così com'è scritta (min sui primi) l'enunciato è tautologico. La prova del paper parla del min su **tutti** gli N. Quella versione vale per t > 0 ma non per t ≤ 0 (N = 1). Proposta: enunciare per `t ≥ log 3` (dominio della Def. 2) `min{N ≥ 1 : log S_N ≥ t} = N(t)` ed è primo. |
| A4 | Prop. 3(b) | classe (ii), Landau come ipotesi | **Classe (i)**: è `prop30_two_imp_RH 1` di arcs-algo, dimostrato senza ipotesi. `momentError 1 x = Σ_{p≤x} p − ∫_2^x t/log t = S(x) − B(x)`, esattamente. Serve solo un'ipotesi unilaterale e la si chiede sui naturali N ≥ 2: è più debole di quella del paper, quindi il teorema Lean implica quello del paper. Il codice (Landau, LandauMellin, LandauZeros, ZeroSingularity, ZetaNegative, Prop30 e parte di ArcProp3) va estratto in lean-base: ★★★ di lavoro meccanico. |
| A5 | G3 | solo il passo 2, t = 3/2 | È più ampio. Il passo 1 enuncia la formula troncata "per t ≥ 3/2", e il passo 3 usa il bound su `R(t,T)` per ogni t ∈ [3/2, x]. Entrambi escono dal dominio x ≥ 2 (vedi §5). |
| A6 | Lemma J | `J₀ ≥ 0` su [0, 2] usando il primo zero 2,404… | Non serve: la stessa serie alternante dà `J₀(x) ≥ 1 − x²/4 ≥ 0` per `|x| ≤ 2`. La prova del Lemma J diventa autonoma (serie alternante a termini decrescenti, rapporto ≤ y/(k+1)²). Il resto della prova dell'audit è corretto: `c₂ = y²/4`, `c₃ = 5y³/36`, `c₃/c₂ = 5y/9`. |
| A7 | Teor. 4(a) | foglie RvM, Lindeberg, Pólya | Confermate; il calcolo `∫_0^∞ log(γ/2π)/(A²+γ²) dγ = (π/2A)log(A/2π)` e quindi `σ_a² ∼ log(A/2π)/(2A)` torna. Mathlib ha solo il TLC i.i.d. |
| A8 | Teor. 1 | PNT come ipotesi | lean-base ha già `m·Δ_m → 2` (`r_asymp`) da `PNTcons`. Scelta da fare: `PNTcons` come ipotesi (come ARCS: è una conseguenza del PNT, non il PNT) oppure `PNT` come ipotesi più `PNT ⇒ PNTcons` da dimostrare (★★★). La seconda è più fedele. |
| A9 | §8.1 | non trattato | La formula di f(u) è scritta con la somma non troncata su γ > 0, che non converge assolutamente. La forma rigorosa è lo Step 4 con T = e^Y. Va enunciata così. |
| A10 | §8.3 | non trattato | "Ripple ≍ e^{−t/4}" e "Θ > ½ ⇒ ripple ≍ e^{−(1−Θ)t/2}": il paper dimostra solo la stima superiore (Prop. 3(a)). La stima inferiore richiede un Ω-teorema e il paper non la dimostra. Non è un enunciato numerato: va lasciata fuori, oppure detta come limite del paper. |
| A11 | Cor. 2 | — | `o(1)` per t → ∞, uniforme in t′ ≥ t: i quantificatori vanno fissati in Lean; il paper non li scrive. |
| A12 | Oss. operatore | "CHIUSA, opzionale" | L'autoaggiunzione dell'operatore diagonale illimitato non è comoda in Mathlib (★★★★). Si può prendere solo `dist(t, {σ_m}) → 0` (★). |
| — | G1, G2, G4 | | Confermati così come sono scritti. |

## 5. G3: dominio della formula esplicita troncata

Fonte consultata: A. Strömbergsson, *Analytic Number Theory — Lecture notes based on Davenport's book*
(Uppsala 2008), §13 "The explicit formula for ψ(x) (Davenport Chapter 17)",
https://www2.math.uu.se/~ast10761/analtalt08/www_notes.pdf. **Il libro di Davenport non era
disponibile:** la citazione con la pagina va controllata sul volume (GTM 74, 3ª ed., cap. 17, pp. 104–110).

- **Teorema 13.2** (la forma troncata di Davenport): *per ogni x ≥ 2 e T ≥ 2*,
  `ψ₀(x) = x − Σ_{|γ|<T} x^ρ/ρ − ζ′(0)/ζ(0) − ½ log(1 − x^{−2}) + R(x,T)`, con
  `|R(x,T)| ≪ x log²(xT)/T + (log x) min(1, x/(T⟨x⟩))`. Qui `⟨x⟩` è la distanza dalla potenza di primo più vicina diversa da x, e la costante è assoluta.
- **Teorema 13.1** (forma esatta, von Mangoldt): *per ogni x > 1*, con la somma simmetrica `lim_{T→∞} Σ_{|γ|<T}`. Le note la dimostrano per x ≥ 2 e lasciano 1 < x < 2 come esercizio (Problem 13.1).

**Conclusione.** La forma troncata con quel resto è enunciata per x ≥ 2. Il paper la usa a t = 3/2 (passo 2) e per t ∈ [3/2, 2) (passi 1 e 3): fuori dal dominio citato.

**Riparazioni possibili** (decide l'autore):
1. A t = 3/2 basta la forma esatta (x > 1): `Σ_{|γ|<T} (3/2)^ρ/ρ` converge per T → ∞, quindi è limitata uniformemente in T ≥ 2. Questo chiude il passo 2, ma non il bound su [3/2, 2) del passo 3.
2. *Proposta*: limite inferiore 5/2 invece di 3/2. Vale `Π_a(x) = 2^a + ∫_{5/2}^x t^a/log t dψ` per x ≥ 5/2, perché il salto di ψ in 2 dà il solo termine `2^a`. Inoltre ⟨5/2⟩ = 1/2, e la formula si usa solo per t ≥ 5/2 ≥ 2. Il termine `2^a` è O(1) e finisce nel resto. Cambiano solo costanti.

Altre due differenze da annotare: Davenport usa ψ₀ e `|γ| < T`, il paper ψ e `|γ| ≤ T`. In Lean l'ipotesi va scritta come in Davenport.

## 6. Proposta per gli enunciati dei teoremi principali (namespace `CPS`)

Indici del paper (`p₁ = 2`) in CpsLean, con un lemma ponte verso `LeanBase.PrimeSums.p (m−1)`.

**Blocco A — solo Mathlib e lean-base (da fare per primo).**
1. Definizioni: `CPS.prime m` (`p_m`), `CPS.S N`, `CPS.sigma m`, `CPS.firstCrossing t` (N(t)),
   `CPS.eps t`, `CPS.step m` (Δ_m), `CPS.cellIndex t` (m(t)), `CPS.cell t` (δ(t)).
2. `CPS.prop1_crossing_prime`: ∀ t ≥ log 3, `N(t)` è primo e `N(t) = min{N ≥ 1 : log S_N ≥ t}` (A3).
3. `CPS.theorem2_covering`: (a) ∀ m ≥ 1, `p_{m+1} ≤ S(p_m)`; (b) ∀ m ≥ 1, `Δ_m ≤ log 2 ∧ (Δ_m = log 2 ↔ m = 1)`;
   (c) `ε(log 3) = 0`; (d) ∀ t > log 3, `0 ≤ ε(t) ∧ ε(t) < δ(t) ∧ δ(t) ≤ log 2`.
4. `CPS.sigma_strictMono` (Def. 1) e `CPS.step_eq` (`Δ_m = log(1 + p_{m+1}/S_{p_m})`).
5. `CPS.brown_remark`: ∀ m ≥ 1, `p_{m+1} ≤ S(p_m) + 1` e ogni T con 1 ≤ T ≤ S(p_m) è somma di un
   sottoinsieme di `{1, p_1, …, p_m}`.
6. `CPS.prop3b_ripple_imp_RH`: `(∀ ε > 0, ∃ C, ∀ x ≥ 2, |S(x) − B(x)| ≤ C x^{3/2+ε}) → RiemannHypothesis`,
   con `B(x) = 1 + ∫_2^x t/log t dt`, che è `1 + li(x²) − li(4)` senza valore principale. Si dimostra riusando arcs-algo.
7. `CPS.lemmaJ`: `|x| ≤ 2 → 0 ≤ J₀ x ∧ J₀ x ≤ exp(−x²/4)`, con `CPS.besselJ0` definita come serie.
8. Opzionali (★): `CPS.integerGrid_step` (RI), `CPS.remark1_integral` (R1, solo l'integrale),
   `CPS.layers_identity` (NT, `Π_a = Σ_k θ_{ka}(x^{1/k})/k`), `CPS.step3_layers` per a ≥ 0 (ST3),
   `CPS.reducedResidue_uniform` (RU), `CPS.dist_sigma_tendsto_zero` (RD).

**Blocco B — con ipotesi classiche dichiarate.**
9. `CPS.theorem1_step` (i) e (ii), `CPS.theorem2_asymp`, `CPS.prop2_scaling`, `CPS.cor2_halfExponent`, tutti da `PNT`
   (oppure da `PNTcons`: decisione A8).
10. `CPS.prop3a_RH_imp_ripple`: RH, `VonKochPsi`.
11. `CPS.step2_bias_layer`: PNT pesato. Con il solo PNT si ottiene (1 + o(1)) (G1); con `O(1/log x)`
    serve il PNT con resto: decisione da prendere.
12. Più avanti, dopo una decisione sull'infrastruttura degli zeri (somma su `|γ| ≤ T` con molteplicità):
    Lemma A (con la riparazione di G3), Teor. 3(i), Teor. 3(ii), Teor. 4(a), con le ipotesi del §3.
    Il Teor. 4(b) resta fuori.

**Numerici.** `N₁ = 4691` e `S(4691) = 1 378 036` per calcolo nel kernel, se si chiude senza
`native_decide`. Il primo attraversamento a x = 109 entra come certificato con script (serve `li(109²)`).

Stima di dimensione: il blocco A e i punti 9–11 stanno largamente sotto le 300 righe di enunciati.
