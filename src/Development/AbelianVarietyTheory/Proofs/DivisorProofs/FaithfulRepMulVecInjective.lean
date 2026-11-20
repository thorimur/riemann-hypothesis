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
import Std.Tactic.BVDecide.Normalize.Prop
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem torsionFree_of_finite_domain_action
    (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ]
    [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ)
    (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R)
    (ha : a ≠ 0) (hx : (ρ a).mulVec x = 0) : x = 0 := by
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have halg : IsAlgebraic R a := hint.isAlgebraic
  obtain ⟨c, hc, a', hca⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
  have hc0 : c ≠ 0 := by
    exact hc
  have key : c • x = 0 := by
    have h1 : ρ (algebraMap R Λ c) = c • (1 : Matrix (Fin h) (Fin h) R) := by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    have h2 : (ρ (algebraMap R Λ c)).mulVec x = c • x := by
      rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← h2, hca, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  funext i
  have hi : c * x i = 0 := by simpa using congrFun key i
  simpa [hc0] using hi

theorem torsionFree_of_finite_domain_action' :
    ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 :=
  fun R Λ _ _ _ _ _ _ _ h ρ a x ha hx => torsionFree_of_finite_domain_action R Λ h ρ a x ha hx

end GlobalTheory
