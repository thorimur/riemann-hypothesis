import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
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

open AlgebraicGeometry CategoryTheory

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

def IsMonomialIn (E : List X.IdealSheafData) (M : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
    M.comap U.ι = ∏ i : Fin E.length, (E.get i).comap U.ι ^ a i

structure IsMonomialSplitting (E : List X.IdealSheafData) (I M N : X.IdealSheafData) :
    Prop where
  eq_mul : I = M * N
  monomial_support : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)
  monomial : IsMonomialIn E M
  transversal : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
    (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
    ¬ C ⊆ (N.support : Set X)

end FunctorialResolution.EmbeddedResolution
