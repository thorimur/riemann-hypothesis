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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

theorem trace_matrix_pi_operator : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  intro W _ _ _ m h A
  have key : ∀ k j : Fin m, LinearMap.trace ℂ (Fin m → W)
      (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ LinearMap.proj j)
      = if k = j then LinearMap.trace ℂ W A else 0 := by
    intro k j
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    by_cases hkj : k = j
    · subst hkj
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, if_pos rfl]
    · rw [LinearMap.proj_comp_single_ne (R := ℂ) (φ := fun _ : Fin m => W) j k (Ne.symm hkj), LinearMap.comp_zero, map_zero, if_neg hkj]
  simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]

end GlobalTheory
