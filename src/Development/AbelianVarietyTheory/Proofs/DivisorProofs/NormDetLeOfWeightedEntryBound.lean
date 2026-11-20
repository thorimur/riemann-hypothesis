import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_det_le_of_weighted {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) (c : ℝ) (hw : ∀ a, 0 < w a)
    (h : ∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  have hM : ∀ i b, ‖M i b‖ ≤ |c| * ((w (u i))⁻¹ * (w b)⁻¹) := by
    intro i b
    have hp : 0 < w (u i) * w b := mul_pos (hw _) (hw _)
    rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact (h i b).trans (le_abs_self c)
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ ≤ |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ i, |c| * ((w (u (σ i)))⁻¹ * (w i)⁻¹) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
          have e : ∏ i, (w (u (σ i)))⁻¹ = ∏ a, (w a)⁻¹ :=
            Equiv.prod_comp (σ.trans u) (fun a => (w a)⁻¹)
          rw [e, ← Finset.prod_mul_distrib]
          simp only [sq]
  rw [Matrix.det_apply']
  calc _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

end GlobalTheory.GoodTop
