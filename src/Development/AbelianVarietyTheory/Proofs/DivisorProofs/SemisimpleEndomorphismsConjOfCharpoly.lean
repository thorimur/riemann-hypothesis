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

open Polynomial Module

namespace GlobalTheory.SemisimpleConj

variable {K : Type} [Field K]

noncomputable def actX (K : Type) [Field K] (M : Type) [AddCommGroup M] [Module K[X] M] [Module K M]
    [IsScalarTower K K[X] M] : Module.End K M :=
  Algebra.lsmul K K M (X : K[X])

section
variable {M : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]

instance finiteDimensional_submodule [FiniteDimensional K M] (S : Submodule K[X] M) :
    FiniteDimensional K S :=
  FiniteDimensional.of_injective ((S.subtype).restrictScalars K) Subtype.val_injective

end

section
variable {M N : Type} [AddCommGroup M] [Module K[X] M] [Module K M] [IsScalarTower K K[X] M]
  [AddCommGroup N] [Module K[X] N] [Module K N] [IsScalarTower K K[X] N]

end

end GlobalTheory.SemisimpleConj
