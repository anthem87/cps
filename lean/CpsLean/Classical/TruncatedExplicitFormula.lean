module

public import CpsLean.Zeros
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
set_option autoImplicit false

/-!
# The truncated explicit formula for `ψ`, as an explicit hypothesis

`TruncatedExplicitFormula`: for `x ≥ 2` and `T ≥ 2`,
`ψ₀(x) = x − Σ_{|γ|<T} x^ρ/ρ − ζ′(0)/ζ(0) − ½ log(1 − x^{−2}) + R(x, T)`, with
`|R(x, T)| ≪ x log²(xT)/T + log x · min(1, x/(T⟨x⟩))`. It is used in Step 1 of the proof of
Theorem 3 (Lemma A), with the lower limit `5/2` of DIVERGENZE.md, D2, so only for `x ≥ 5/2`.
-/

open Real

@[expose] public section

namespace CpsLean

/-- **Truncated explicit formula for `ψ`** [H. Davenport, *Multiplicative Number Theory*, 3rd ed.,
GTM 74, Ch. 17, (9)–(10); A. Strömbergsson, *Analytic Number Theory, lecture notes based on
Davenport's book*, Uppsala 2008, Thm. 13.2]: there is an absolute constant `C` such that, for every
real `x ≥ 2` and `T ≥ 2`,
`|ψ₀(x) − (x − Σ_{|γ|<T} x^ρ/ρ − ζ′(0)/ζ(0) − ½ log(1 − x^{−2}))| ≤
C (x log²(xT)/T + log x · min(1, x/(T⟨x⟩)))`, the sum over the nontrivial zeros with
multiplicity and `⟨x⟩` the distance from `x` to the nearest prime power other than `x`. Domain as
in Strömbergsson's statement; the page in Davenport is to be checked on the volume. An explicit
hypothesis, never an axiom. -/
def TruncatedExplicitFormula : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖((psi0 x : ℝ) : ℂ) - ((x : ℂ) - zeroSumLt T (fun ρ => (x : ℂ) ^ ρ / ρ)
        - deriv riemannZeta 0 / riemannZeta 0 - ((1 / 2 * log (1 - x ^ (-2 : ℤ)) : ℝ) : ℂ))‖ ≤
      C * (x * log (x * T) ^ 2 / T + log x * min 1 (x / (T * primePowerDist x)))

end CpsLean
