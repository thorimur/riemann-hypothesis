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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]

variable {A}

@[simp] theorem peirceProjection_apply (e : R) (he : IsIdempotentElem e) (x : A) :
    peirceCut A e he x = e • x + (1 - e) • (1 : A) := rfl

end GlobalTheory.PeirceDecompositionCut
