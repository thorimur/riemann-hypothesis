import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SectionsPinch

theorem app_eq_of_factor {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ]
    (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O)
    (hfac : O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ) :
    j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op =
      κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  have key : ∀ (f g : O.toScheme ⟶ Y), f = g → ∀ e e',
      f.appLE κ.opensRange ⊤ e = g.appLE κ.opensRange ⊤ e' := by
    rintro f g rfl e e'; rfl
  have hle' : ⊤ ≤ (O.ι ≫ j) ⁻¹ᵁ κ.opensRange := fun x _ ↦
    (hO.ge x.2 : _)
  rw [← cancel_mono O.topIso.inv]
  have lhs : (j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op) ≫ O.topIso.inv =
      (O.ι ≫ j).appLE κ.opensRange ⊤ hle' := by
    show j.appLE κ.opensRange O hO.ge ≫ O.topIso.inv = _
    rw [← Scheme.Hom.appLE_comp_appLE O.ι j κ.opensRange O ⊤ hO.ge (fun x _ ↦ x.2)]
    congr 1
    rw [Scheme.Opens.topIso_inv]
    exact (Scheme.Opens.ι_appLE O O ⊤ _).symm
  rw [lhs, key _ _ hfac hle' (hfac ▸ hle')]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
  rw [← Scheme.Hom.appLE_comp_appLE O.toSpecΓ (Spec.map q ≫ κ) κ.opensRange ⊤ ⊤
      (fun x _ ↦ ⟨_, rfl⟩) le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map q) κ κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨x, rfl⟩) le_top,
    Category.assoc]
  have top : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = f.appTop :=
    fun f _ ↦ Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  rw [← top (Spec.map q) le_top, ← top O.toSpecΓ le_top]

end GlobalTheory.SectionsPinch
