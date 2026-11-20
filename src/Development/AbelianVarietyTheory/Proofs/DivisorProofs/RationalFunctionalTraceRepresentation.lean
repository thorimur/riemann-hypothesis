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
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

theorem linearMap_rat_valued_eq_trace : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  intro E _ _ g hg
  choose f hf using hg
  let g' : E →ₗ[ℚ] ℚ :=
    { toFun := f
      map_add' := by
        intro x y
        apply (Rat.cast_injective (α := ℝ))
        rw [Rat.cast_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := by
        intro c x
        apply (Rat.cast_injective (α := ℝ))
        rw [smul_eq_mul, RingHom.id_apply, Rat.cast_mul, ← hf, ← hf, map_smul, Rat.smul_def] }
  have hB := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual _ hB).symm g', fun z => ?_⟩
  have h1 : (LinearMap.BilinForm.toDual _ hB ((LinearMap.BilinForm.toDual _ hB).symm g')) z = g' z := by
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
  rw [h1]
  exact hf z

end GlobalTheory
