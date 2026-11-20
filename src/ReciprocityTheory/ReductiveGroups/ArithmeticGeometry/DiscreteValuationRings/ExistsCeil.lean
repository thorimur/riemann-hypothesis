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

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

theorem reps_X {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ) (hk : 1 ≤ k) :
    ∃ rep : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ χ : X, ∃ a μ, rep a + k • μ = χ) ∧
      (∀ a a' (μ μ' : X), rep a + k • μ = rep a' + k • μ' → a = a') ∧
      (∀ x y : X, k • x = k • y → x = y) := by
  classical
  let b := Module.finBasis ℤ X
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun a => b.equivFun.symm (fun i => ((a i : ℕ) : ℤ)), ?_, ?_, ?_⟩
  · intro χ
    refine ⟨fun i => ⟨(b.equivFun χ i % k).toNat, ?_⟩, b.equivFun.symm (fun i => b.equivFun χ i / k), ?_⟩
    · rw [Int.toNat_lt (Int.emod_nonneg _ hk0.ne')]
      exact Int.emod_lt_of_pos _ hk0
    · apply b.equivFun.injective
      funext i
      simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')]
      exact Int.emod_add_mul_ediv _ _
  · intro a a' μ μ' h
    funext i
    have e := congrFun (congrArg b.equivFun h) i
    simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply] at e
    have e' := congrArg (fun t => t % (k : ℤ)) e
    rw [Int.add_mul_emod_self_left, Int.add_mul_emod_self_left] at e'
    have e1 : ((a i : ℕ) : ℤ) % k = (a i : ℕ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a i).isLt)
    have e2 : ((a' i : ℕ) : ℤ) % k = (a' i : ℕ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a' i).isLt)
    rw [e1, e2] at e'
    exact Fin.ext (by exact_mod_cast e')
  · intro x y hxy
    apply b.equivFun.injective
    funext i
    have e := congrFun (congrArg b.equivFun hxy) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk0.ne' e

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
