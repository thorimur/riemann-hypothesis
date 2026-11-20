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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.DualFlag

theorem abel_sum_rev : ∀ (n : ℕ) (b : Fin (n + 1) → ℝ) (e : Fin (n + 2) → ℝ), e 0 = 0 →
    (∑ i : Fin (n + 1), b i * (e i.rev.succ - e i.rev.castSucc)) =
      (∑ i : Fin n, (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc)) +
        b 0 * e (Fin.last (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro b e h0
    simp [h0]
  | succ n ih =>
    intro b e h0
    have h := ih (fun i => b i.succ) (fun i => e i.castSucc) (by simpa using h0)
    have hL := Fin.sum_univ_succ (fun i : Fin (n + 2) => b i * (e i.rev.succ - e i.rev.castSucc))
    have hR := Fin.sum_univ_succ
      (fun i : Fin (n + 1) => (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc))
    simp only [Fin.rev_succ, Fin.rev_zero, Fin.succ_last, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.succ_castSucc] at h hL hR
    rw [hL, hR]
    linear_combination h

end GlobalTheory.CompanionTheory.DualFlag
