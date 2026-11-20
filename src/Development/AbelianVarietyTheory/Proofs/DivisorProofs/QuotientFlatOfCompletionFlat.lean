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
import Mathlib.RingTheory.AdicCompletion.Algebra
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
open TensorProduct

theorem GlobalTheory.flat_quot_of_flat_adicCompletion : ∀ (A : Type) [CommRing A] (f : A) (M : Type) [AddCommGroup M] [Module A M],
  Module.Flat (AdicCompletion (Ideal.span {f}) A) (TensorProduct A (AdicCompletion (Ideal.span {f}) A) M) →
  Module.Flat (A ⧸ Ideal.span {f}) (TensorProduct A (A ⧸ Ideal.span {f}) M) := by
  intro A _ f M _ _ hflat
  set I : Ideal A := Ideal.span {f}
  let φ : AdicCompletion I A →ₐ[A] A ⧸ I :=
    (Ideal.quotientEquivAlgOfEq A (pow_one I)).toAlgHom.comp (AdicCompletion.evalₐ I 1)
  letI : Algebra (AdicCompletion I A) (A ⧸ I) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A (AdicCompletion I A) (A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    exact (φ.commutes a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A (AdicCompletion I A) (A ⧸ I) (A ⧸ I) M
  haveI : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[AdicCompletion I A] (AdicCompletion I A ⊗[A] M)) := inferInstance
  exact Module.Flat.of_linearEquiv e.symm
