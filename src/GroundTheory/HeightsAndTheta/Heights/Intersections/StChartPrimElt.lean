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

open Polynomial

def ChartPrimElt.Statement : Prop :=
  ∀ (Φ : Type) [Field Φ] [CharZero Φ] (Φ' : Type) [Field Φ'] [Algebra Φ Φ'] (Q : Type) [Fintype Q]
    (r : Q → Φ'),
    FiniteDimensional Φ (IntermediateField.adjoin Φ (Set.range r)) →
    ∃ (τ : MvPolynomial Q Φ) (g : Q → Φ[X]) (u : Φ[X]),
      (minpoly Φ (MvPolynomial.aeval r τ)).natDegree =
        Module.finrank Φ (IntermediateField.adjoin Φ (Set.range r)) ∧
      (∀ q, aeval (MvPolynomial.aeval r τ) (g q) = r q) ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ u * derivative (minpoly Φ (MvPolynomial.aeval r τ)) - 1 ∧
      minpoly Φ (MvPolynomial.aeval r τ) ∣ MvPolynomial.aeval g τ - X ∧
      ∀ q, r q ≠ 0 → ∃ h : Φ[X], minpoly Φ (MvPolynomial.aeval r τ) ∣ h * g q - 1

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
