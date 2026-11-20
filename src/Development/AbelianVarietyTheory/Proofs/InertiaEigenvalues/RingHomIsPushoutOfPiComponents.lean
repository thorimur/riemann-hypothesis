import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open TensorProduct

namespace GlobalTheory

theorem isPushout_of_pi_components_alg {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A']
    [CommRing P'] {n : ℕ} {Q Q' : Fin n → Type} [∀ i, CommRing (Q i)] [∀ i, CommRing (Q' i)]
    [Algebra A P] [Algebra A A'] [Algebra P P'] [Algebra A' P'] [Algebra A P']
    [IsScalarTower A P P'] [IsScalarTower A A' P']
    [∀ i, Algebra A (Q i)] [∀ i, Algebra (Q i) (Q' i)] [∀ i, Algebra A' (Q' i)]
    [∀ i, Algebra A (Q' i)] [∀ i, IsScalarTower A (Q i) (Q' i)] [∀ i, IsScalarTower A A' (Q' i)]
    (g : ∀ i, P →ₐ[A] Q i) (g' : ∀ i, P' →ₐ[A'] Q' i)
    (hg : Function.Bijective (fun (x : P) (i : Fin n) => g i x))
    (hg' : Function.Bijective (fun (x : P') (i : Fin n) => g' i x))
    (hk : ∀ i x, g' i (algebraMap P P' x) = algebraMap (Q i) (Q' i) (g i x))
    (H : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i)) : Algebra.IsPushout A A' P P' := by
  have hpi := IsBaseChange.pi (S := A') (fun i => (IsScalarTower.toAlgHom A (Q i) (Q' i)).toLinearMap)
    (fun i => (H i).out)
  let e : P ≃ₗ[A] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g i).toLinearMap) hg
  let e' : P' ≃ₗ[A'] (∀ i, Q' i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g' i).toLinearMap) hg'
  refine ⟨IsBaseChange.of_equiv
    (LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hpi.equiv ≪≫ₗ e'.symm) fun x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul]
  funext i
  exact (hk i x).symm

theorem isPushout_of_pi_components : ∀ {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A'] [CommRing P'] {n : ℕ}
    {Pi P'i : Fin n → Type} [∀ i, CommRing (Pi i)] [∀ i, CommRing (P'i i)]
    (f : A →+* P) (k : A →+* A') (k' : P →+* P') (h' : A' →+* P')
    (g : ∀ i, P →+* Pi i) (g' : ∀ i, P' →+* P'i i) (kk : ∀ i, Pi i →+* P'i i) (hh : ∀ i, A' →+* P'i i),
    Function.Bijective (fun (x : P) (i : Fin n) => g i x) →
    Function.Bijective (fun (x : P') (i : Fin n) => g' i x) →
    (∀ i, (g' i).comp k' = (kk i).comp (g i)) → (∀ i, (g' i).comp h' = hh i) →
    (∀ i, CategoryTheory.IsPushout (CommRingCat.ofHom ((g i).comp f)) (CommRingCat.ofHom k)
      (CommRingCat.ofHom (kk i)) (CommRingCat.ofHom (hh i))) →
    CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom k) (CommRingCat.ofHom k')
      (CommRingCat.ofHom h') := by
  intro A P A' P' _ _ _ _ n Q Q' _ _ f k k' h' g g' kk hh hg hg' hk hh' H
  have hw : ∀ i a, kk i (g i (f a)) = hh i (k a) := fun i a =>
    congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of (Q' i) => φ.hom a) (H i).w
  have hk1 : ∀ i x, g' i (k' x) = kk i (g i x) := fun i x => RingHom.congr_fun (hk i) x
  have hh1 : ∀ i x, g' i (h' x) = hh i x := fun i x => RingHom.congr_fun (hh' i) x
  have hc : ∀ a, k' (f a) = h' (k a) := fun a => hg'.1 (funext fun i => by
    show g' i (k' (f a)) = g' i (h' (k a))
    rw [hk1, hh1, hw])
  letI : Algebra A P := f.toAlgebra
  letI : Algebra A A' := k.toAlgebra
  letI : Algebra P P' := k'.toAlgebra
  letI : Algebra A' P' := h'.toAlgebra
  letI : Algebra A P' := (k'.comp f).toAlgebra
  haveI : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun a => hc a
  letI : ∀ i, Algebra A (Q i) := fun i => ((g i).comp f).toAlgebra
  letI : ∀ i, Algebra (Q i) (Q' i) := fun i => (kk i).toAlgebra
  letI : ∀ i, Algebra A' (Q' i) := fun i => (hh i).toAlgebra
  letI : ∀ i, Algebra A (Q' i) := fun i => ((kk i).comp ((g i).comp f)).toAlgebra
  haveI : ∀ i, IsScalarTower A (Q i) (Q' i) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, IsScalarTower A A' (Q' i) := fun i => IsScalarTower.of_algebraMap_eq fun a => hw i a
  have H' : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i) := fun i =>
    (CommRingCat.isPushout_iff_isPushout.mp (H i)).symm
  have := isPushout_of_pi_components_alg (A := A) (P := P) (A' := A') (P' := P') (Q := Q) (Q' := Q')
    (fun i => { g i with commutes' := fun _ => rfl })
    (fun i => { g' i with commutes' := fun a => hh1 i a }) hg hg' hk1 H'
  exact CommRingCat.isPushout_iff_isPushout.mpr this.symm

end GlobalTheory
