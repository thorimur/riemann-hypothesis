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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

noncomputable section
namespace GlobalTheory.GeomPointLift

theorem nonempty_algHom_of_isAlgClosed (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (C ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ M)
  exact ⟨(IsAlgClosed.lift : (C ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hft : Algebra.FiniteType A B) (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  letI : Algebra A k := φ.toAlgebra
  haveI : Nontrivial (k ⊗[A] B) := Module.FaithfullyFlat.rTensor_nontrivial A B k
  haveI : Algebra.FiniteType k (k ⊗[A] B) := inferInstance
  obtain ⟨f⟩ := nonempty_algHom_of_isAlgClosed k (k ⊗[A] B)
  refine ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A k (k ⊗[A] B), AlgHom.commutes]
  rfl

end GlobalTheory.GeomPointLift

example : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := GlobalTheory.GeomPointLift.exists_lift
