import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

abbrev epsAt (x : Spec (CommRingCat.of R) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)

def IsTanAt (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (v : epsAt x ⟶ G) : Prop :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left

def epsMul (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def dualMap (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

structure LieModel (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
    [Module R E] where

  pt : E → (epsAt x ⟶ G)
  tan : ∀ e, IsTanAt G x (pt e)
  inj : Function.Injective pt
  onto : ∀ v, IsTanAt G x v → ∃ e, pt e = v
  add : ∀ e e', pt (e + e') = pt e * pt e'
  smul : ∀ (c : R) e, (pt (c • e)).left = Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (pt e).left

def LieModel.IsDiffOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) (f : G ⟶ G) (A : E →ₗ[R] E) : Prop :=
  ∀ e, M.pt (A e) = M.pt e ≫ f

def LieModel.IsActOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End R E) : Prop :=
  ∀ a, M.IsDiffOf (act a) (ρ a)

def eigSp {E : Type} [AddCommGroup E] [Module R E] {O : Type} [CommRing O] (ρ : O →+* Module.End R E)
    (σ : O →+* R) : Submodule R E :=
  ⨅ a, LinearMap.ker (ρ a - σ a • LinearMap.id)

end GlobalTheory.CompanionTheory.Ar
