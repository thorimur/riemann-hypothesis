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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open scoped Matrix

namespace GlobalTheory

theorem mem_span_image_of_orthogonal_rational_annihilator :
    ∀ (F R : Type) [Field F] [CommRing R] [Algebra F R] (κ : Type) [Fintype κ] (A : Set (κ → F)) (x : κ → R),
    (∀ y : κ → F, (∀ a ∈ A, a ⬝ᵥ y = 0) → x ⬝ᵥ (fun i => algebraMap F R (y i)) = 0) →
    x ∈ Submodule.span R ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) := by
  intro F R _ _ _ κ _ A x hx
  classical
  set W := Submodule.span F A with hW
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  set P : (κ → F) →ₗ[F] (κ → F) := W.subtype ∘ₗ Submodule.linearProjOfIsCompl W C hC with hP
  have hPW : ∀ v, P v ∈ W := fun v => (Submodule.linearProjOfIsCompl W C hC v).2
  have hPa : ∀ a ∈ W, P a = a := fun a ha => by
    have h := Submodule.linearProjOfIsCompl_apply_left hC ⟨a, ha⟩
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val h
  set S := ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) with hS
  have hφ : ∀ v ∈ W, (fun i => algebraMap F R (v i)) ∈ Submodule.span R S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero =>
        convert Submodule.zero_mem (Submodule.span R S) using 1
        ext i; simp
    | add u w _ _ hu hw =>
        convert add_mem hu hw using 1
        ext i; simp
    | smul c u _ hu =>
        convert Submodule.smul_mem _ (algebraMap F R c) hu using 1
        ext i; simp
  let e : κ → κ → F := fun j => fun i => if j = i then 1 else 0
  have key : ∀ k, x k = ∑ j, x j * algebraMap F R (P (e j) k) := by
    intro k
    let g : (κ → F) →ₗ[F] F := LinearMap.proj k ∘ₗ (LinearMap.id - P)
    have hy : ∀ a ∈ A, a ⬝ᵥ (fun j => g (e j)) = 0 := by
      intro a ha
      have h1 : g a = 0 := by
        simp [g, hPa a (Submodule.subset_span ha)]
      rw [← h1, LinearMap.pi_apply_eq_sum_univ g a]
      simp [dotProduct, e]
    have h := hx _ hy
    simp [dotProduct, g, e, mul_sub, Finset.sum_sub_distrib] at h
    rw [sub_eq_zero] at h
    simpa [e] using h
  have hx' : x = ∑ j, x j • (fun i => algebraMap F R (P (e j) i)) := by
    funext k
    rw [key k]
    simp [Finset.sum_apply]
  rw [hx']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφ _ (hPW _))

end GlobalTheory
