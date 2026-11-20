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

theorem UpperTheory.Reformulated.B.Qf45.isInt_conj :
    ∀ {O : Type} [inst : CommRing O]
    {B : Type} [inst_1 : Ring B] [inst_2 : Algebra O B] (a b k : B),
    a * b = (1 : B) → b * a = (1 : B) → IsIntegral O k → IsIntegral O (a * k * b) := by
  intro O _ B _ _ a b k hab hba hk
  let f : B →ₐ[O] B :=
    { toFun := fun x => a * x * b
      map_one' := by rw [mul_one, hab]
      map_mul' := fun x y => by
        calc a * (x * y) * b = a * x * (b * a) * y * b := by
              rw [hba, mul_one, mul_assoc a x y]
          _ = a * x * b * (a * y * b) := by simp only [mul_assoc]
      map_zero' := by rw [mul_zero, zero_mul]
      map_add' := fun x y => by rw [mul_add, add_mul]
      commutes' := fun r => by
        rw [← Algebra.commutes r a, mul_assoc, hab, mul_one] }
  exact hk.map f
