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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.finExt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
      (φ : A →+* B) (f : A →+* V), Function.Injective φ → φ.Finite → Function.Injective f →
      ∃ (y : B →+* V) (s : Finset K), y.comp φ = f ∧ ∀ b, (y b : K) ∈ Subfield.closure (Set.range (V.subtype.comp f) ∪ s) := by
  intro K _ _ V A B _ _ _ _ φ f hφ hfin hf
  classical
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A K := (V.subtype.comp f).toAlgebra
  letI : Algebra A V := f.toAlgebra
  haveI : Module.Finite A B := hfin
  have hfK : Function.Injective (V.subtype.comp f) := Subtype.val_injective.comp hf
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK
  haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  let y₀ : B →ₐ[A] K := IsAlgClosed.lift
  have hmem : ∀ b, y₀ b ∈ V := by
    intro b
    have h1 : IsIntegral A (y₀ b) := (Algebra.IsIntegral.isIntegral b).map y₀
    have h2 : IsIntegral V (y₀ b) := h1.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hz]
    exact z.2
  let y : B →+* V := y₀.toRingHom.codRestrict V hmem
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine ⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩
  · ext a
    exact y₀.commutes a
  · intro b
    show y₀ b ∈ _
    have hb : b ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Subfield.subset_closure
      right
      simp
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x z _ _ hx hz =>
      rw [map_add]
      exact add_mem hx hz
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem (Subfield.subset_closure ?_) hx
      left
      exact ⟨a, rfl⟩
