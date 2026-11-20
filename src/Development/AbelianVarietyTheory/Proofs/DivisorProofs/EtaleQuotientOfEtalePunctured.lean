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
open IsLocalRing

namespace GlobalTheory

theorem etale_quotient_of_etale_punctured :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R)
      [IsLocalRing (R ⧸ Ideal.span {f})],
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) →
        Algebra.Etale (Localization.AtPrime P)
          (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P)
            (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  intro R A _ _ _ _ f _ H P _ hP
  set S := R ⧸ Ideal.span {f}
  set T := Localization.AtPrime P
  set p : Ideal R := P.comap (algebraMap R S) with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    rw [← h] at hr
    exact hr
  haveI := H p hp
  let φ : Localization.AtPrime p →+* T := Localization.localRingHom p P (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R T r = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])
  haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T
      (TensorProduct R (Localization.AtPrime p) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A
  let e2 := Algebra.TensorProduct.cancelBaseChange R S T T A
  let e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S))
  let e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T]
      TensorProduct S T (TensorProduct R S A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e3
  exact Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)

end GlobalTheory
