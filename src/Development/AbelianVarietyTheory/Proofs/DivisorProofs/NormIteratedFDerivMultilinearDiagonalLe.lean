import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem norm_iteratedFDeriv_diag_multilinear_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  set L : E →L[ℝ] (Fin j → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E) with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 (fun _ => ?_)
    simp [hL]
  have hfun : (fun y : E => f (fun _ => y)) = (f : (Fin j → E) → ℂ) ∘ L := by
    funext z; simp [hL]
  have hf : ContDiff ℝ ⊤ (f : (Fin j → E) → ℂ) := f.contDiff
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L hf y (by exact_mod_cast le_top)]
  have hLy : ‖L y‖ ≤ ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 (fun _ => ?_)
    simp [hL]
  calc ‖(iteratedFDeriv ℝ i (⇑f) (L y)).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * ∏ _ : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    _ = ‖iteratedFDeriv ℝ i (⇑f) (L y)‖ := mul_one _
    _ ≤ (Fintype.card (Fin j)).descFactorial i * ‖f‖ * ‖L y‖ ^ (Fintype.card (Fin j) - i) :=
        f.norm_iteratedFDeriv_le i (L y)
    _ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
        rw [Fintype.card_fin]
        gcongr

end GlobalTheory
