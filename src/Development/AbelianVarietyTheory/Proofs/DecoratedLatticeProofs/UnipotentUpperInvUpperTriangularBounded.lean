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
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem unipotent_upper_inv_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  intro N C
  refine ⟨(Nat.factorial N : ℝ) * (max C 1) ^ N, ?_⟩
  intro n hd hl hb
  have htri : n.BlockTriangular id := fun i j h => hl i j h
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]; simp [hd]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  refine ⟨n⁻¹, Matrix.nonsing_inv_mul n hu, Matrix.mul_nonsing_inv n hu, ?_, ?_⟩
  · intro i j h
    letI := Matrix.invertibleOfIsUnitDet n hu
    exact Matrix.blockTriangular_inv_of_blockTriangular htri h
  · intro i j
    have hinv : n⁻¹ = n.adjugate := by rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have key := Matrix.det_le (abv := AbsoluteValue.abs) (x := max C 1)
      (A := n.updateRow j (Pi.single i 1)) ?_
    · simpa using key
    · intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hk]
        exact le_trans (hb k l) (le_max_left _ _)

end GlobalTheory
