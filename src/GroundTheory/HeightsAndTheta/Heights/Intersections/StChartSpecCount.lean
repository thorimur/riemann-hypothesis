import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

def ChartSpecCount.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ']
    (φ : R →+* Φ) (Q : Type) [Fintype Q] (r : Q → Φ'),
    (∀ c : Φ, ∃ f g : R, φ g ≠ 0 ∧ c = φ f / φ g) →
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ E : R, φ E ≠ 0 ∧ ∀ ψ : R →+* ℂ, RingHom.ker φ ≤ RingHom.ker ψ → ψ E ≠ 0 →
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.Finite ∧
      {y : Q → ℂ | ∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0}.ncard =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      ∀ y : Q → ℂ, (∀ F : MvPolynomial Q R, MvPolynomial.eval₂ ((algebraMap Φ Φ').comp φ) r F = 0 →
          MvPolynomial.eval₂ ψ y F = 0) → ∀ q, r q ≠ 0 → y q ≠ 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
