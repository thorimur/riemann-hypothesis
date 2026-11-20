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

namespace GlobalTheory

theorem sum_mem_span_range_le_of_isSimpleModule :
    ∀ (A P M : Type) [Ring A] [Algebra ℂ A] [AddCommGroup P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M], IsSimpleModule A P →
    ∀ (n : ℕ) (T : Fin n → P →ₗ[A] M) (ξ : Fin n → P) (N : Submodule A M), ∑ i, T i (ξ i) ∈ N →
      ∑ i, T i (ξ i) ∈ Submodule.span ℂ {x | ∃ (S : P →ₗ[A] M) (y : P), LinearMap.range S ≤ N ∧ x = S y} := by
  intro A P M _ _ _ _ _ _ _ _ _ _ hP n T ξ N hN
  classical
  let F : (Fin n → P) →ₗ[A] M := ∑ i, (T i).comp (LinearMap.proj i)
  have hF : ∀ y, F y = ∑ i, T i (y i) := by
    intro y
    simp [F, LinearMap.sum_apply]
  let D : Submodule A (Fin n → P) := N.comap F
  obtain ⟨C, hC⟩ := exists_isCompl D
  let G : (Fin n → P) →ₗ[A] M := F.comp (D.subtype.comp (D.projectionOnto C hC))
  have hGN : ∀ y, G y ∈ N := fun y => ((D.projectionOnto C hC) y).2
  have hξD : ξ ∈ D := by
    show F ξ ∈ N
    rw [hF]; exact hN
  have hGξ : G ξ = ∑ i, T i (ξ i) := by
    have : D.projectionOnto C hC ξ = ⟨ξ, hξD⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨ξ, hξD⟩
    simp only [G, LinearMap.comp_apply, this, Submodule.subtype_apply]
    exact hF ξ
  rw [← hGξ, ← Finset.univ_sum_single ξ, map_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  refine ⟨G.comp (LinearMap.single A (fun _ : Fin n => P) i), ξ i, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hGN _
  · simp

end GlobalTheory
