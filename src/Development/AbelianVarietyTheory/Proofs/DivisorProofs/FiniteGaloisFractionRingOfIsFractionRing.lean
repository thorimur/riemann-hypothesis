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

theorem _root_.GlobalTheory.finiteGalois_fractionRing_of_isFractionRing :
    ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  intro A K L _ _ _ _ _ _ _ _ _ _ h
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  letI alg : Algebra (FractionRing A) L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hmap : ∀ y : FractionRing A, algebraMap (FractionRing A) L y = algebraMap K L (e y) :=
    fun _ => rfl
  have hcomp : (algebraMap (FractionRing A) L).comp (e.symm.toRingEquiv : K →+* FractionRing A) =
      ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap K L) := by
    ext x; simp [hmap]
  refine ⟨alg, IsScalarTower.of_algebraMap_eq fun a => ?_, ?_, ?_, ?_⟩
  · rw [hmap, AlgEquiv.commutes, h]
  · exact Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp
  · exact IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv) (g := RingEquiv.refl L) hcomp
  · intro σ x
    have := σ.commutes (e.symm x)
    simpa [hmap] using this

end GlobalTheory
