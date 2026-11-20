import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem app_surj {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (f.app U).hom :=
  f.app_surjective U hU

theorem fromSpec_appLE_top {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D)
    (e : (⊤ : (Spec Γ(Y, D)).Opens) ≤ hD.fromSpec ⁻¹ᵁ D) :
    hD.fromSpec.appLE D ⊤ e = (Scheme.ΓSpecIso Γ(Y, D)).inv := by
  unfold Scheme.Hom.appLE
  rw [hD.fromSpec_app_self]
  simp [← Functor.map_comp]

theorem SpecMap_appLE_top {R S : CommRingCat.{0}} (f : R ⟶ S) (e : (⊤ : (Spec S).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem appLE_fromSpec_quot {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) (J : Ideal Γ(Y, D))
    (e : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec) ⁻¹ᵁ D) (x : Γ(Y, D)) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec).appLE D ⊤ e).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J x) := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ D ⊤ ⊤ (by simp [hD.fromSpec_preimage_self]) (by simp)]
  rw [fromSpec_appLE_top, SpecMap_appLE_top]
  change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J
    ((Scheme.ΓSpecIso Γ(Y, D)).hom.hom ((Scheme.ΓSpecIso Γ(Y, D)).inv.hom x))) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem ker_snd {W Z Y : Scheme.{0}} (i : W ⟶ Z) [IsClosedImmersion i] (π : Y ⟶ Z) (V : Z.Opens) (hV : IsAffineOpen V)
    (D : Y.Opens) (hD : IsAffineOpen D) (hDV : D ≤ π ⁻¹ᵁ V) :
    RingHom.ker ((pullback.snd i π).app D).hom = Ideal.map (π.appLE V D hDV).hom (RingHom.ker (i.app V).hom) := by
  apply le_antisymm
  · set I := RingHom.ker (i.app V).hom
    set J := Ideal.map (π.appLE V D hDV).hom I
    have hI' : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
    have hsurj := i.app_surjective V hV
    let e := RingHom.quotientKerEquivOfSurjective hsurj
    have hIJ : I ≤ J.comap (π.appLE V D hDV).hom := Ideal.le_comap_map
    let ψ : Γ(W, i ⁻¹ᵁ V) →+* Γ(Y, D) ⧸ J := (Ideal.quotientMap J (π.appLE V D hDV).hom hIJ).comp e.symm.toRingHom
    let a : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec
    let w : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ W := Spec.map (CommRingCat.ofHom ψ) ≫ hI'.fromSpec
    have hring : i.appLE V (i ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom ψ =
        π.appLE V D hDV ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      rw [← Scheme.Hom.app_eq_appLE]
      have : e.symm ((i.app V).hom x) = Ideal.Quotient.mk I x := by
        rw [RingEquiv.symm_apply_eq]; rfl
      change Ideal.quotientMap J (π.appLE V D hDV).hom hIJ (e.symm ((i.app V).hom x)) = _
      rw [this, Ideal.quotientMap_mk]
    have hw : w ≫ i = a ≫ π := by
      simp only [w, a, Category.assoc]
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec i hV hI' le_rfl,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π hV hD hDV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
    let c := pullback.lift w a hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have he : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤ a ⁻¹ᵁ D := by
      simp [a, hD.fromSpec_preimage_self]
    have h0 : (a.appLE D ⊤ he).hom x = 0 := by
      have hca : c ≫ pullback.snd i π = a := pullback.lift_snd _ _ _
      have key : ∀ (b : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y) (hb : c ≫ pullback.snd i π = b) (e' : ⊤ ≤ b ⁻¹ᵁ D),
          (b.appLE D ⊤ e').hom x = 0 := by
        rintro b rfl e'
        rw [← Scheme.Hom.appLE_comp_appLE _ _ D ((pullback.snd i π) ⁻¹ᵁ D) ⊤ le_rfl (by simpa using e'),
          ← Scheme.Hom.app_eq_appLE]
        simp [hx]
      exact key a hca he
    rw [appLE_fromSpec_quot hD J he x] at h0
    have h1 : Ideal.Quotient.mk J x = 0 := by
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).hom.hom h0
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h2
      exact h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [RingHom.mem_ker] at hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 : ∀ (f : pullback i π ⟶ Z) (hf : pullback.fst i π ≫ i = f) (e : (pullback.snd i π) ⁻¹ᵁ D ≤ f ⁻¹ᵁ V),
        (f.appLE V _ e).hom g = 0 := by
      rintro f rfl e
      rw [Scheme.Hom.comp_appLE]
      simp [hg]
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact h1 _ pullback.condition _

end CrystallineSemistableComparison.Onto.CLB

end
