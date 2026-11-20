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
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_surj_pi_quot_pow_ker_eq {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A) :
    P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d →
      ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧
        ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  intro hP r d hd
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨0, ?_, ?_⟩
    · intro y
      refine ⟨0, ?_⟩
      funext i
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i)
      rw [← ha]
      exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simp)).symm
    · intro x
      simp
  haveI : P.IsPrime := hP.isPrime
  have hPr : P ^ r ≠ ⊤ := by
    intro h
    exact hP.ne_top (eq_top_iff.mpr (h ▸ Ideal.pow_le_self hr.ne'))
  haveI : Nontrivial (A ⧸ P ^ r) := Ideal.Quotient.nontrivial_iff.2 hPr
  let Ap := Localization.AtPrime P
  let φ : Ap →ₐ[A] A ⧸ P ^ r := IsLocalization.liftAlgHom (M := P.primeCompl)
    (f := Ideal.Quotient.mkₐ A (P ^ r)) fun u ↦
      Ideal.Quotient.isUnit_mk_pow_of_notMem _ (Ideal.mem_primeCompl_iff.mp u.prop)
  letI : Algebra Ap (A ⧸ P ^ r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A Ap (A ⧸ P ^ r) := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm

  haveI : Module.Free Ap (Ap ⊗[A] M) := Module.free_of_flat_of_isLocalRing
  have hle := Ideal.primeCompl_le_nonZeroDivisors P
  have hAp : Module.finrank Ap (Ap ⊗[A] M) = d := by
    rw [IsLocalization.finrank_eq Ap P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl (TensorProduct.mk A Ap M 1) hle, hd]
  let e0 := TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap (A ⧸ P ^ r) (A ⧸ P ^ r) M
  haveI : Module.Free (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := Module.Free.of_equiv e0
  haveI : Module.Finite (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := inferInstance
  have hB : Module.finrank (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) = d := by
    rw [← e0.finrank_eq, Module.finrank_baseChange, hAp]
  let e : (A ⧸ P ^ r) ⊗[A] M ≃ₗ[A ⧸ P ^ r] (Fin d → A ⧸ P ^ r) :=
    (Module.finBasisOfFinrankEq _ _ hB).equivFun
  let g : M →ₗ[A] (Fin d → A ⧸ P ^ r) :=
    (e.restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (A ⧸ P ^ r) M 1
  refine ⟨g, ?_, ?_⟩
  · exact e.surjective.comp (TensorProduct.mk_surjective A M (A ⧸ P ^ r) Ideal.Quotient.mk_surjective)
  · intro x
    have h1 : g x = 0 ↔ (1 : A ⧸ P ^ r) ⊗ₜ[A] x = 0 := by
      simp [g, e.map_eq_zero_iff]
    rw [h1, ← (quotTensorEquivQuotSMul M (P ^ r)).map_eq_zero_iff]
    have h2 : (1 : A ⧸ P ^ r) = Ideal.Quotient.mk (P ^ r) 1 := rfl
    rw [h2, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

end GlobalTheory
