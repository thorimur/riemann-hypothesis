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
import Mathlib.Tactic.ENatToNat
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlobalTheory.SectionsCommRing

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

def structureHom (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom

theorem map_structureHom (s : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (structureHom s U r) = structureHom s V r := by
  show ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = _
  rw [← X.presheaf.map_comp]
  rfl

def Sections (_s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Type u := Γ(X, U)

namespace Sections

variable (s : X ⟶ Spec (CommRingCat.of R))

instance (U : X.Opens) : CommRing (Sections s U) := inferInstanceAs (CommRing Γ(X, U))

instance (U : X.Opens) : Algebra R (Sections s U) :=
  RingHom.toAlgebra (R := R) (S := Sections s U) (structureHom s U)

def equiv (U : X.Opens) : Sections s U ≃+* Γ(X, U) := RingEquiv.refl _

theorem equiv_apply (U : X.Opens) (a : Sections s U) : equiv s U a = a := rfl

def restrict {U V : X.Opens} (h : V ≤ U) : Sections s U →ₐ[R] Sections s V where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := map_structureHom s h r

theorem restrict_restrict {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (a : Sections s U) :
    restrict s k (restrict s h a) = restrict s (k.trans h) a := by
  show ((X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE k).op).hom a) =
    (X.presheaf.map (homOfLE (k.trans h)).op).hom a
  rw [← X.presheaf.map_comp]
  rfl

end Sections

end GlobalTheory.SectionsCommRing
