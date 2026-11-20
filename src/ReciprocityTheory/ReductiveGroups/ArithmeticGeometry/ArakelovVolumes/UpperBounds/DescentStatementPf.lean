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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

open scoped TensorProduct
open Module

variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]

theorem indep_iff {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by
  constructor
  · intro hv
    exact Module.Flat.linearIndependent_one_tmul hv
  · intro h
    have h' : LinearIndependent F (fun i => (1 : F') ⊗ₜ[F] v i) :=
      h.restrict_scalars' F
    exact LinearIndependent.of_comp (TensorProduct.mk F F' V 1) h'

end ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

end ReciprocityTheory.ChartRestriction.G.AR.Up
