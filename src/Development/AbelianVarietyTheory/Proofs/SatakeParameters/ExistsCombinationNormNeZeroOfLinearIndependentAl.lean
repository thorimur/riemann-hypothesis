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
open scoped TensorProduct
open Matrix

namespace GlobalTheory

theorem exists_combination_norm_ne_zero_of_linearIndependent
    {B A : Type} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] {d : ℕ} (hd : Module.finrank B A = d)
    (y : Fin d → A) (hy : LinearIndependent B y) :
    ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  classical
  let e := Module.finBasisOfFinrankEq B A hd
  let Y : Matrix (Fin d) (Fin d) B := fun i j => e.equivFun (y j) i
  have key : ∀ v : Fin d → B, e.equivFun (∑ j, v j • y j) = Y *ᵥ v := by
    intro v
    ext i
    simp [Y, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : Y.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : ∑ j, v j • y j = 0 := by
      apply e.equivFun.injective
      rw [key, hv, map_zero]
    exact hv0 (funext fun j => Fintype.linearIndependent_iff.mp hy v h1 j)
  refine ⟨Y.adjugate *ᵥ e.equivFun 1, ?_⟩
  have hsum : ∑ j, (Y.adjugate *ᵥ e.equivFun 1) j • y j = algebraMap B A Y.det := by
    apply e.equivFun.injective
    rw [key, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
  rw [hsum, Algebra.norm_algebraMap]
  exact pow_ne_zero _ hdet

end GlobalTheory
