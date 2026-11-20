import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem residueFieldMap_surjective_of_isClosedImmersion
    (X Y : AlgebraicGeometry.Scheme.{0}) (i : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion i]
    (x : X) : Function.Surjective (i.residueFieldMap x).hom := by
  have h1 : Function.Surjective (i.stalkMap x).hom := i.stalkMap_surjective x
  have h2 : Function.Surjective (X.residue x).hom := X.residue_surjective x
  have h3 : Function.Surjective (Y.residue (i x) ≫ i.residueFieldMap x).hom := by
    rw [Scheme.residue_residueFieldMap]
    exact h2.comp h1
  exact Function.Surjective.of_comp (g := (Y.residue (i x)).hom) h3

end GlobalTheory
