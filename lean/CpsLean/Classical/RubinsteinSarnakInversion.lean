module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false

/-!
# The inversion formula of Rubinstein–Sarnak, as an explicit hypothesis

For a symmetric law with integrable characteristic function,
`P(Z > b) = ½ − (1/π) ∫_0^∞ sin(bξ)/ξ · φ̂(ξ) dξ`. It gives the formula for `δ_a` in Step 6 of the
proof of Theorem 3(ii).
-/

open Real MeasureTheory Set

@[expose] public section

namespace CpsLean

/-- **Inversion formula** [M. Rubinstein, P. Sarnak, *Chebyshev's bias*, Experiment. Math. 3
(1994), §3; J. Gil-Pelaez, *Note on the inversion theorem*, Biometrika 38 (1951)]: if `ν` is a
probability measure on `ℝ`, symmetric about `0`, whose characteristic function
`φ̂(ξ) = ∫ e^{iξt} dν(t)` (real, by symmetry) is integrable, then for every `b > 0`,
`ν((b, ∞)) = ½ − (1/π) ∫_0^∞ sin(bξ)/ξ · φ̂(ξ) dξ`. An explicit hypothesis, never an axiom. -/
def RubinsteinSarnakInversion : Prop :=
  ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ).map (fun t => -t) = ν →
    Integrable (charFun (ν : Measure ℝ)) → ∀ b : ℝ, 0 < b →
      (ν : Measure ℝ).real (Ioi b) =
        1 / 2 - 1 / π * ∫ ξ in Ioi (0 : ℝ), sin (b * ξ) / ξ * (charFun (ν : Measure ℝ) ξ).re

end CpsLean
