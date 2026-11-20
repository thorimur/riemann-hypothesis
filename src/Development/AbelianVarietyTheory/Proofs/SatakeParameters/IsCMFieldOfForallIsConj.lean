import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField NumberField.ComplexEmbedding

namespace GlobalTheory.CMFieldCriterion

theorem isTotallyReal_fixedField (K : Type) [Field K] [NumberField K] {σ : Gal(K/ℚ)}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsTotallyReal (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
  dsimp only
  rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
    ComplexEmbedding.isReal_iff]
  ext x
  have hx : σ (x : K) = x :=
    (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)
  have h := (hσ W.embedding).eq (x : K)
  rw [hx] at h
  rw [conjugate_coe_eq]
  exact h.symm

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    {σ : Gal(K/ℚ)} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : σ ≠ 1 :=
    (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hne
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact isConj_apply_apply (hσ φ) x
  have hreal := isTotallyReal_fixedField K hσ
  have hquad :
      Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K :=
    { finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }
  exact IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K

end GlobalTheory.CMFieldCriterion
