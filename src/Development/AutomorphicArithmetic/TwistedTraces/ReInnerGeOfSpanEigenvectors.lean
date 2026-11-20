import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.re_inner_ge_of_span_eigenvectors :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (T : Module.End ℂ M) (c : ℝ) (s : Set M), (∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (T x)) (j y) = inner ℂ (j x) (j (T y))) → (∀ x ∈ s, x ∈ V ∧ ∃ κ : ℂ, -c ≤ κ.re ∧ T x = κ • x) → ∀ v ∈ Submodule.span ℂ s, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (T v))).re := by
  intro M H _ _ _ _ j V T c s hsym hs v hv
  classical
  have hle : Submodule.span ℂ s ≤
      ⨆ κ : {κ : ℂ // -c ≤ κ.re}, (V ⊓ Module.End.eigenspace T (κ : ℂ)) := by
    refine Submodule.span_le.2 fun x hx => ?_
    obtain ⟨hxV, κ, hκ, hT⟩ := hs x hx
    exact Submodule.mem_iSup_of_mem (⟨κ, hκ⟩ : {κ : ℂ // -c ≤ κ.re})
      ⟨hxV, Module.End.mem_eigenspace_iff.2 hT⟩
  obtain ⟨f, hf, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hV : ∀ κ, f κ ∈ V := fun κ => (hf κ).1
  have hT : ∀ κ, T (f κ) = (κ : ℂ) • f κ := fun κ => Module.End.mem_eigenspace_iff.1 (hf κ).2
  have hrel : ∀ a b : {κ : ℂ // -c ≤ κ.re}, (starRingEnd ℂ) (a : ℂ) * inner ℂ (j (f a)) (j (f b))
      = (b : ℂ) * inner ℂ (j (f a)) (j (f b)) := by
    intro a b
    have := hsym _ (hV a) _ (hV b)
    rwa [hT, hT, map_smul, map_smul, inner_smul_left, inner_smul_right] at this
  have horth : ∀ a b, a ≠ b → inner ℂ (j (f a)) (j (f b)) = 0 := by
    intro a b hab
    by_cases h0 : j (f a) = 0
    · rw [h0, inner_zero_left]
    · have h1 : (starRingEnd ℂ) (a : ℂ) = a :=
        mul_right_cancel₀ (fun h => h0 (inner_self_eq_zero.1 h)) (hrel a a)
      have h2 := hrel a b
      rw [h1] at h2
      by_contra h3
      exact hab (Subtype.ext (mul_right_cancel₀ h3 h2))
  have hv' : v = ∑ a ∈ f.support, f a := hfv.symm
  have e1 : inner ℂ (j v) (j v) = ∑ a ∈ f.support, inner ℂ (j (f a)) (j (f a)) := by
    rw [hv', map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha]
    intro b _ hb
    exact horth a b hb.symm
  have e2 : inner ℂ (j v) (j (T v))
      = ∑ a ∈ f.support, (a : ℂ) * inner ℂ (j (f a)) (j (f a)) := by
    rw [hv', map_sum T, map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha, hT, map_smul, inner_smul_right]
    intro b _ hb
    rw [hT, map_smul, inner_smul_right, horth a b hb.symm, mul_zero]
  have hn : ∀ x : H, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e3 : ‖j v‖ ^ 2 = ∑ a ∈ f.support, ‖j (f a)‖ ^ 2 := by
    simp only [hn] at e1
    exact_mod_cast e1
  rw [e2, e3, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hn, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right a.2 (sq_nonneg _)
