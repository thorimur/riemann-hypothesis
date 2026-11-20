import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace Bl.general_b_fact_second_last

theorem goal1 :
  ∀ (B : Int) {S : Nat} (c : Fin S → Int),
  (∀ (m : Fin S), LT.lt.{0} (abs.{0} (c m)) B) →
    Eq.{1} (Finset.sum.{0, 0} Finset.univ.{0} fun (m : Fin S) ↦ HMul.hMul.{0, 0, 0} (c m) (HPow.hPow.{0, 0, 0} B m.val))
        0 →
      ∀ (m : Fin S), Eq.{1} (c m) 0 := by
  intro B S
  induction S with
  | zero => intro c _ _ m; exact m.elim0
  | succ n ih =>
    intro c hc hs m
    have hB : 0 < B := lt_of_le_of_lt (abs_nonneg _) (hc 0)
    rw [Fin.sum_univ_succ] at hs
    have h2 : ∑ i : Fin n, c i.succ * B ^ (i.succ).val = B * ∑ i : Fin n, c i.succ * B ^ i.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [h2, Fin.val_zero, pow_zero, mul_one] at hs
    have hd : B ∣ c 0 := ⟨-(∑ i : Fin n, c i.succ * B ^ i.val), by rw [mul_neg]; linarith⟩
    have h0 : c 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (hc 0)
    rw [h0, zero_add] at hs
    have hT : ∑ i : Fin n, c i.succ * B ^ i.val = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact absurd h hB.ne'
      · exact h
    have ih' := ih (fun i => c i.succ) (fun i => hc _) hT
    exact Fin.cases h0 (fun i => ih' i) m

end Bl.general_b_fact_second_last
