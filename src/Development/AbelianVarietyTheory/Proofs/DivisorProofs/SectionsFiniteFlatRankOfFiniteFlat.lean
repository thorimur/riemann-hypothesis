import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem isPullback_fromSpec_app_preimage_of_affine {X T : Scheme.{0}} (p : X ⟶ T) {U : T.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (p.app U)) p hU.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec p hU hV]) (by simp)).flip

theorem sections_finite_flat_rank_of_finite_flat :
    ∀ (X T : Scheme.{0}) (p : X ⟶ T) [IsFinite p] [Flat p] (r : ℕ), (∀ t, p.finrank t = r) →
      ∀ (U : T.Opens), IsAffineOpen U → letI := (p.app U).hom.toAlgebra;
      Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧
        ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(X, p ⁻¹ᵁ U) q = r := by
  intro X T p _ _ r hr U hU
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  have hpb := isPullback_fromSpec_app_preimage_of_affine p hU hV
  have hfin : IsFinite (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb ‹_›
  have hflat : Flat (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb ‹_›
  have h1 : (p.app U).hom.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have h2 : (p.app U).hom.Flat := Flat.SpecMap_iff.1 hflat
  letI := (p.app U).hom.toAlgebra
  haveI : Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h1
  haveI : Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h2
  refine ⟨inferInstance, inferInstance, fun q ↦ ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb q
  rw [hr] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory
