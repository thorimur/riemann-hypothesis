import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrincipalModRadical

open GlobalTheory.CechPic GlobalTheory.LamOfDouble

theorem surjective_of_finite {R A : Type} [CommRing R] [CommRing A] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (φ : R →+* A) (hφ : φ.Finite) (h : ∀ a, ∃ r, a - φ r ∈ J.map φ) : Function.Surjective φ := by
  algebraize [φ]
  have key : (⊤ : Submodule R A) ≤ LinearMap.range (Algebra.linearMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ fun a _ => ?_
    obtain ⟨r, hr⟩ := h a
    rw [← add_sub_cancel (φ r) a]
    refine Submodule.add_mem_sup ⟨r, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact hr
  exact fun a => key (Submodule.mem_top (x := a))

theorem mono_of_section {R : Type} [CommRing R] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of R)) [IsFinite f] (e : Spec (CommRingCat.of R) ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Spec (CommRingCat.of (R ⧸ J))),
      d ≫ f = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) → d = d ≫ f ≫ e) : Mono f := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.isoSpec.inv ≫ f)
  obtain ⟨ε, hε⟩ := Spec.map_surjective (e ≫ H.isoSpec.hom)
  have fin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let q : Γ(H, ⊤) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let τ : CommRingCat.of (R ⧸ J) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) :=
    CommRingCat.ofHom (Ideal.quotientMap _ φ.hom Ideal.le_comap_map)
  have h₁ := h _ (Spec.map q ≫ H.isoSpec.inv) (Spec.map τ) (by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
    rfl)
  have h₂ : q = ε ≫ φ ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ, hε, ← cancel_mono H.isoSpec.inv, h₁]
    simp
  have sur : Function.Surjective φ.hom := surjective_of_finite J hJ φ.hom fin fun a =>
    ⟨ε.hom a, Ideal.Quotient.eq.1 (congrArg (fun g => g.hom a) h₂)⟩
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ sur
  have e' : f = H.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  rw [e']
  infer_instance

end GlobalTheory.PrincipalModRadical
