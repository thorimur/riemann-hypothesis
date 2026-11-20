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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.CompanionTheory.Ggeo.HomDual

noncomputable def homEquivDual (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] :
    (P →ₗ[R] Localization.Away f) ≃ₗ[Localization.Away f] Module.Dual (Localization.Away f) P :=
  { toFun := fun g =>
      LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f) g
    invFun := fun g => g.restrictScalars R
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finite_projective_hom : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P] [Module.Projective (Localization.Away f) P],
    Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧
      Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  intro R P _ f _ _ _ _ _ _
  let e := homEquivDual R P f
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end GlobalTheory.CompanionTheory.Ggeo.HomDual
