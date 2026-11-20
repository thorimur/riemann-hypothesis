import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
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
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem baseChange_field_fibre_isPreirreducible :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] (X X' : AlgebraicGeometry.Scheme.{0}) (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) (p : X' ⟶ X) (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of K')), CategoryTheory.IsPullback p g' g (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K'))) → ∀ x : X, (letI : Algebra K (X.residueField x) := (AlgebraicGeometry.Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra; IsDomain (TensorProduct K (X.residueField x) K')) → IsPreirreducible ((⇑p) ⁻¹' {x}) := by
  intro K K' _ _ _ X X' g p g' h x hd
  letI : Algebra K (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra
  have h1 : IsPullback (p.fiberι x) (p.fiberToSpecResidueField x) p (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  have h3 := h1.paste_horiz h.flip
  have hg : X.fromSpecResidueField x ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap K (X.residueField x))) := by
    rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ g)]
    rfl
  rw [hg] at h3
  let e : p.fiber x ≅ Spec (.of (TensorProduct K (X.residueField x) K')) :=
    h3.flip.isoPullback ≪≫ pullbackSpecIso K (X.residueField x) K'
  have : IsIntegral (Spec (.of (TensorProduct K (X.residueField x) K'))) := inferInstance
  have : IsIntegral (p.fiber x) := IsIntegral.of_isIso e.inv
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (p.fiberι x).continuous.continuousOn

end GlobalTheory
