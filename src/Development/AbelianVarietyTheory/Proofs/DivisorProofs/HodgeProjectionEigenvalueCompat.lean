import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Eigenspace.Basic
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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem eigenvector_mem_ker_of_ne_coord_char :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  intro W _ _ g Λ P hspan Q hQ O T χ hΛ hT ψ hψ w hw

  let D : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a =>
    { toFun := fun v j => χ a j * v j
      map_add' := by intro u v; funext j; simp [mul_add]
      map_smul' := by intro c v; funext j; simp; ring }
  have hcomm : ∀ a, Q ∘ₗ T a = D a ∘ₗ Q := by
    intro a
    refine LinearMap.ext_on_range hspan ?_
    intro x
    have h1 : T a (P x) = P ⟨_, hΛ a x⟩ := hT a x ⟨_, hΛ a x⟩ rfl
    simp only [LinearMap.comp_apply, h1, hQ]
    rfl
  rw [LinearMap.mem_ker]
  have hw' : ∀ a, T a w = ψ a • w := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    exact Module.End.mem_eigenspace_iff.1 this
  funext j
  obtain ⟨a, ha⟩ := hψ j
  have h2 := congrArg (fun f => f w) (hcomm a)
  simp only [LinearMap.comp_apply, hw', map_smul] at h2
  have h3 := congrFun h2 j
  change ψ a * Q w j = χ a j * Q w j at h3
  have h4 : (χ a j - ψ a) * Q w j = 0 := by rw [sub_mul, ← h3]; ring
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd (sub_eq_zero.1 h) ha
  · simpa using h

end GlobalTheory
