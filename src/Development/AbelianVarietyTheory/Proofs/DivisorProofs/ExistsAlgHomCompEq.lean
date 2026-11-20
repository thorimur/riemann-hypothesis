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
import Mathlib.Order.CompletePartialOrder
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

namespace GlobalTheory.GroupBplus

theorem exists_algHom_comp_eq {A K C : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] (f : C →ₐ[A] K) :
    ∃ g : C →ₐ[A] A, (Algebra.ofId A K).comp g = f := by
  have h : ∀ c, f c ∈ (⊥ : Subalgebra A K) := fun c => by
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((Algebra.IsIntegral.isIntegral (R := A) c).map f)
    exact Algebra.mem_bot.2 ⟨a, ha⟩
  let e := Algebra.botEquivOfInjective (IsFractionRing.injective A K)
  refine ⟨e.toAlgHom.comp (f.codRestrict ⊥ h), ?_⟩
  ext c
  have h1 := congrArg Subtype.val (e.symm.commutes (e (f.codRestrict ⊥ h c)))
  rw [Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.symm_apply_apply] at h1
  exact h1.symm

end GlobalTheory.GroupBplus
