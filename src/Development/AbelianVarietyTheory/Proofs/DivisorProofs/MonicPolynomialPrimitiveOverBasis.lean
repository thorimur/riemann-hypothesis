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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open Polynomial

namespace GlobalTheory

open IntermediateField.algebraAdjoinAdjoin in
theorem exists_monic_integral_primitive_multiple : ∀ (k C : Type) [Field k] [Field C] [Algebra k C] (d : ℕ) (t : Fin d → C) (α : C), AlgebraicIndependent k t → IsAlgebraic (IntermediateField.adjoin k (Set.range t)) α → ∃ (θ : C) (P : Polynomial (MvPolynomial (Fin d) k)), P.Monic ∧ Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ P = 0 ∧ IsAlgebraic (IntermediateField.adjoin k (Set.range t)) θ ∧ α ∈ IntermediateField.adjoin (IntermediateField.adjoin k (Set.range t)) {θ} ∧ ∀ R : Polynomial (MvPolynomial (Fin d) k), Polynomial.eval₂ (MvPolynomial.aeval t).toRingHom θ R = 0 → P ∣ R := by
  intro k C _ _ _ d t α ht hα
  set A := Algebra.adjoin k (Set.range t) with hAdef
  set K0 := IntermediateField.adjoin k (Set.range t) with hK0def
  have hαA : IsAlgebraic A α := (IsFractionRing.isAlgebraic_iff A K0 C).mpr hα
  obtain ⟨y, hy0, hyint⟩ := hαA.exists_integral_multiple
  set θ := y • α with hθ
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A := ht.aevalEquiv
  haveI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have he : ∀ p : MvPolynomial (Fin d) k, algebraMap A C (e p) = MvPolynomial.aeval t p := by
    intro p
    exact ht.algebraMap_aevalEquiv p
  have hcomp : (MvPolynomial.aeval t).toRingHom.comp e.symm.toRingEquiv.toRingHom = algebraMap A C := by
    ext a
    simp [← he]
  have hcomp2 : (algebraMap A C).comp e.toRingEquiv.toRingHom = (MvPolynomial.aeval t).toRingHom := by
    ext p <;> simp [he]
  refine ⟨θ, (minpoly A θ).map e.symm.toRingEquiv.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact (minpoly.monic hyint).map _
  · rw [eval₂_map, hcomp]
    exact minpoly.aeval A θ
  · exact (hyint.tower_top (A := K0)).isAlgebraic
  · have hyC : (y : C) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hyK : (y : C) ∈ K0 := IntermediateField.algebra_adjoin_le_adjoin k _ y.2
    have hinv : (y : C)⁻¹ ∈ K0 := K0.inv_mem hyK
    have hθmem : θ ∈ IntermediateField.adjoin K0 {θ} := IntermediateField.mem_adjoin_simple_self K0 θ
    have hinvmem : (y : C)⁻¹ ∈ IntermediateField.adjoin K0 {θ} :=
      IntermediateField.algebraMap_mem (IntermediateField.adjoin K0 {θ}) (⟨(y : C)⁻¹, hinv⟩ : K0)
    have : α = (y : C)⁻¹ * θ := by
      rw [hθ, Subalgebra.smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hyC, one_mul]
    rw [this]
    exact mul_mem hinvmem hθmem
  · intro R hR
    have h1 : aeval θ (R.map e.toRingEquiv.toRingHom) = 0 := by
      rw [aeval_def, eval₂_map, hcomp2]; exact hR
    have h2 := Polynomial.map_dvd e.symm.toRingEquiv.toRingHom (minpoly.isIntegrallyClosed_dvd hyint h1)
    rwa [Polynomial.map_map, show e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom = RingHom.id _ by ext p <;> simp, Polynomial.map_id] at h2

end GlobalTheory
