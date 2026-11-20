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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.CuspFormEvaluationComplement

theorem main : ∀ (s : Multiset ℂ) {t : ℝ}, (0 : ℝ) ≤ t → (∀ μ ∈ s, ‖μ - (1 : ℂ)‖ ≤ t) →
    ‖Multiset.prod s - (1 : ℂ)‖ ≤ Real.exp ((↑(Multiset.card s) : ℝ) * t) - (1 : ℝ) := by
  intro s t ht hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a - 1‖ ≤ t := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    rw [Multiset.prod_cons, Multiset.card_cons]
    have hna : ‖a‖ ≤ 1 + t := by
      have h0 : a = (a - 1) + 1 := by ring
      calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [← h0]
        _ ≤ ‖a - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + t := by rw [norm_one]; linarith
    have key : a * s.prod - 1 = a * (s.prod - 1) + (a - 1) := by ring
    have h1 : ‖a * s.prod - 1‖ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t := by
      rw [key]
      calc ‖a * (s.prod - 1) + (a - 1)‖ ≤ ‖a * (s.prod - 1)‖ + ‖a - 1‖ := norm_add_le _ _
        _ = ‖a‖ * ‖s.prod - 1‖ + ‖a - 1‖ := by rw [norm_mul]
        _ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t :=
          add_le_add (mul_le_mul hna ih' (norm_nonneg _) (by linarith)) ha
    have h2 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hE := Real.exp_pos ((Multiset.card s : ℝ) * t)
    have h3 := mul_le_mul_of_nonneg_right h2 hE.le
    have hexp : Real.exp (((Multiset.card s + 1 : ℕ) : ℝ) * t)
        = Real.exp t * Real.exp ((Multiset.card s : ℝ) * t) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hexp]
    nlinarith [h1, h3]

end GlobalTheory.CuspFormEvaluationComplement
