import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace GlobalTheory.SepAffInf

theorem isAffineOpen_inf_of_le_preimage {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h]
    (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens)
    (h₁ : Ω₁.1 ≤ h ⁻¹ᵁ U.1) (h₂ : Ω₂.1 ≤ h ⁻¹ᵁ U.1) : IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  haveI : IsAffine U.1 := U.2
  haveI : (h ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from (h ∣_ U.1)]
    infer_instance
  have key : ∀ Ω : Z.Opens, Ω ≤ h ⁻¹ᵁ U.1 →
      (h ⁻¹ᵁ U.1).ι ''ᵁ ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω) = Ω := by
    intro Ω hΩ
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hΩ
  have a₁ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₁.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₁]
    exact Ω₁.2
  have a₂ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₂.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₂]
    exact Ω₂.2
  have a : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ (Ω₁.1 ⊓ Ω₂.1)) := a₁.inf a₂
  rw [← key _ (inf_le_left.trans h₁)]
  exact a.image_of_isOpenImmersion _

end GlobalTheory.SepAffInf
