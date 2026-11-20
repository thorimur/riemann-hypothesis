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

namespace PeriodicSumRangeMul

private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
