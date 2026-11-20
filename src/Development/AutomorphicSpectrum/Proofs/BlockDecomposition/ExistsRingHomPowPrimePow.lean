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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Frobenius

theorem exists_ringHom_pow_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], (p : A) = 0 → ∀ k : ℕ,
      ∃ F : A →+* A, ∀ x, F x = x ^ p ^ k := by
  intro p hp A _ hpA k
  refine ⟨{ toFun := fun x => x ^ p ^ k
            map_one' := one_pow _
            map_mul' := fun x y => mul_pow x y _
            map_zero' := zero_pow (pow_ne_zero k hp.out.ne_zero)
            map_add' := fun x y => ?_ }, fun x => rfl⟩
  show (x + y) ^ p ^ k = x ^ p ^ k + y ^ p ^ k
  rw [add_pow_prime_pow_eq hp.out x y k, hpA]
  simp only [zero_mul, add_zero]

end GlobalTheory.CompanionTheory.Frobenius
