import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace GlobalTheory.SchwartzDerivativeCompositionBound

theorem norm_iteratedFDeriv_schwartz_comp_clm_le
    {Y F : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Y →L[ℝ] F) (f : SchwartzMap F ℂ) (i : ℕ) (y : Y) :
    ‖iteratedFDeriv ℝ i (fun (z : Y) ↦ (f : F → ℂ) ((L : Y → F) z)) y‖ ≤
      ‖iteratedFDeriv ℝ i (⇑f : F → ℂ) ((L : Y → F) y)‖ * ‖L‖ ^ i := by
  have hf : ContDiff ℝ (i : ℕ) (⇑f : F → ℂ) := f.smooth i
  have h := L.iteratedFDeriv_comp_right hf y (i := i) le_rfl
  have e : (fun (z : Y) ↦ (f : F → ℂ) ((L : Y → F) z)) = (⇑f : F → ℂ) ∘ L := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp

end GlobalTheory.SchwartzDerivativeCompositionBound
