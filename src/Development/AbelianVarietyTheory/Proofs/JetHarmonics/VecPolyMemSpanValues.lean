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

namespace GlobalTheory

theorem vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)

end GlobalTheory
