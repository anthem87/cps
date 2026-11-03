module

public import CpsLean.Zeros
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false

/-!
# The Riemann–von Mangoldt formula, as an explicit hypothesis

`RiemannVonMangoldt`: `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)` as `T → ∞`. It gives the facts
on the zeros used in Lemma A (`Σ_ρ |ρ + a|^{−2} < ∞`), in Step 5 of Theorem 3
(`Σ_{T<γ≤T+1} 1 ≪ log T`) and in Theorem 4(a) (the density `N′(γ) ∼ (1/2π) log(γ/2π)`).
-/

open Real Filter Asymptotics

@[expose] public section

namespace CpsLean

/-- **Riemann–von Mangoldt formula** [H. von Mangoldt, *Zur Verteilung der Nullstellen der
Riemannschen Funktion ξ(t)*, Math. Ann. 60 (1905); H. Davenport, *Multiplicative Number Theory*,
3rd ed., GTM 74, Ch. 15]: the number `N(T)` of nontrivial zeros with `0 < γ ≤ T`, counted with
multiplicity, is `(T/2π) log(T/2π) − T/2π + O(log T)` as `T → ∞`. An explicit hypothesis, never an
axiom. -/
def RiemannVonMangoldt : Prop :=
  (fun T : ℝ => (zeroCount T : ℝ) - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π)))
    =O[atTop] (fun T : ℝ => log T)

end CpsLean
