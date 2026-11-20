import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

variable {T U W : Scheme.{u}}

noncomputable def pullbackSection (g : T ⟶ U) (N : U.Modules) :
    Γ(N, ⊤) →+ Γ((Scheme.Modules.pullback g).obj N, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).app ⊤).hom

lemma pullbackSection_smul (g : T ⟶ U) (N : U.Modules) (a : Γ(U, ⊤)) (n : Γ(N, ⊤)) :
    pullbackSection g N (a • n) = g.appTop a • pullbackSection g N n :=
  Scheme.Modules.Hom.app_smul _ a n

lemma pullbackSection_naturality (g : T ⟶ U) {N N' : U.Modules} (φ : N ⟶ N') (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackSection g N n) =
      pullbackSection g N' (φ.app ⊤ n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm

lemma pullbackComp_inv_pullbackSection (f : W ⟶ T) (g : T ⟶ U) (N : U.Modules) (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) h
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm

end GroundTheory.Arith.Etale
