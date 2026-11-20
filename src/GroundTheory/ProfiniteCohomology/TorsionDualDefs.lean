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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

def QZ : Type := AddCircle (1 : ℚ)

namespace QZ

instance : AddCommGroup QZ := inferInstanceAs (AddCommGroup (AddCircle (1 : ℚ)))

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

instance : IsTopologicalAddGroup QZ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def toAddCircle : QZ ≃+ AddCircle (1 : ℚ) := AddEquiv.refl _

def mk (q : ℚ) : QZ := toAddCircle.symm (q : AddCircle (1 : ℚ))

theorem mk_surjective : Function.Surjective mk := fun x =>
  QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (toAddCircle x)

@[simp] theorem mk_add (p q : ℚ) : mk (p + q) = mk p + mk q := by
  simp [mk]

@[simp] theorem mk_zero : mk 0 = 0 := by simp [mk]

theorem mk_eq_zero_iff (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  simp only [mk, AddEquivClass.map_eq_zero_iff, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]

end QZ

abbrev QZDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Type _ := A →ₜ+ QZ

namespace QZDual

variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]

def map (f : A →ₜ+ B) : QZDual B →ₜ+ QZDual A :=
  ContinuousAddMonoidHom.compLeft QZ f

@[simp]
theorem map_apply (f : A →ₜ+ B) (χ : QZDual B) (a : A) : map f χ a = χ (f a) :=
  rfl

@[simp]
theorem map_id : map (ContinuousAddMonoidHom.id A) = ContinuousAddMonoidHom.id (QZDual A) :=
  rfl

theorem map_comp (g : B →ₜ+ C) (f : A →ₜ+ B) :
    map (g.comp f) = (map f).comp (map g) :=
  rfl

def toAddMonoidHomEquiv [DiscreteTopology A] : QZDual A ≃+ (A →+ QZ) where
  toFun χ := χ.toAddMonoidHom
  invFun f := { f with continuous_toFun := continuous_of_discreteTopology }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem toAddMonoidHomEquiv_apply [DiscreteTopology A] (χ : QZDual A) (a : A) :
    toAddMonoidHomEquiv χ a = χ a :=
  rfl

@[simp]
theorem toAddMonoidHomEquiv_symm_apply [DiscreteTopology A] (f : A →+ QZ) (a : A) :
    toAddMonoidHomEquiv.symm f a = f a :=
  rfl

variable (A) in

def eval : A →+ QZDual (QZDual A) where
  toFun a :=
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_eval_const a }
  map_zero' := by ext χ; exact map_zero χ
  map_add' a b := by ext χ; exact map_add χ a b

@[simp]
theorem eval_apply (a : A) (χ : QZDual A) : eval A a χ = χ a :=
  rfl

end QZDual

end GroundTheory.ProfCoh
