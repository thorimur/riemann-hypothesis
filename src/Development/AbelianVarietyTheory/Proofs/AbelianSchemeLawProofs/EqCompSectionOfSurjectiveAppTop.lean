import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.eq_comp_section_of_surjective_appTop {X T Y : Scheme.{0}} [IsAffine Y] (p : X ⟶ T)
    (ε : T ⟶ X) (g : X ⟶ Y) (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) :
    g = p ≫ ε ≫ g := by
  refine ext_of_isAffine ?_
  ext a
  obtain ⟨b, hb⟩ := hs (g.appTop.hom a)
  have hεp : ε.appTop.hom (p.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← hb, hεp]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.local_rigidity : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g := by
  intro X T Y p ε g h hp hsurj t y hfib
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ) :=
    p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl
  let V : T.Opens := ⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV : t ∈ V := by
    rintro ⟨x, hx, rfl⟩
    exact hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)
  have hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  have hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro s hs
    change p (ε s) ∈ V
    rw [← Scheme.Hom.comp_apply, h]
    exact hs
  haveI : IsAffine W := hW
  refine ⟨V, htV, ?_⟩
  have hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    simp
  have hsV : Function.Surjective (p ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    have hiso := ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
    exact hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))
  have key := congrArg (· ≫ W.ι)
    (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV)
      (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key
  rw [key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι,
    Category.assoc]

end GlobalTheory
