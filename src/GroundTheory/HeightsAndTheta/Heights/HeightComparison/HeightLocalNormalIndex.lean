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
import Mathlib.RingTheory.SimpleRing.Principal
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def LocalNormalIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    ∀ [IsFractionRing O L] (m : Ideal O) [m.IsMaximal],
      (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors).toSubring.toAddSubgroup.relIndex
        (integralClosure (Localization.subalgebra.ofField L m.primeCompl
          m.primeCompl_le_nonZeroDivisors) L).toSubring.toAddSubgroup ≠ 0

example : ∃ (O : Subalgebra ℤ ℚ) (m : Ideal O), Algebra.FiniteType ℤ O ∧
    IsFractionRing O ℚ ∧ m.IsMaximal := by
  let e : (⊥ : Subalgebra ℤ ℚ) ≃ₐ[ℤ] ℤ := Algebra.botEquivOfInjective Int.cast_injective
  have hft : Algebra.FiniteType ℤ (⊥ : Subalgebra ℤ ℚ) := Algebra.FiniteType.equiv inferInstance e.symm
  have hfr : IsFractionRing (⊥ : Subalgebra ℤ ℚ) ℚ := by
    refine IsFractionRing.of_field (⊥ : Subalgebra ℤ ℚ) ℚ fun z ↦ ⟨algebraMap ℤ _ z.num, algebraMap ℤ _ z.den, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp [Rat.num_div_den]
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (⊥ : Subalgebra ℤ ℚ)) bot_ne_top
  exact ⟨⊥, m, hft, hfr, hm⟩

end GroundTheory.Heights₂.Heights
