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
import Mathlib.RingTheory.PowerSeries.Basic
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

open scoped PowerSeries TensorProduct

namespace GlobalTheory

open scoped PowerSeries TensorProduct in

theorem _root_.GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

section Contraction

variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]

end Contraction

section PowerSeries

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Away

variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]

include hϖ

variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]

include h𝔭

end Away

end PowerSeries

universe u

end GlobalTheory
