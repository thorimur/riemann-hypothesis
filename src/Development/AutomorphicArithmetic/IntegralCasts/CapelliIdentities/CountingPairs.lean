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
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable def UpperTheory.Reformulated.B.CountingPairs.rhoPair :
    {n : ℕ} → (Fin n → ℤ) → ℤ :=
    fun {n : ℕ} (l : Fin n → ℤ) ↦ ∑ i : Fin n, ((↑n : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * l i

namespace UpperTheory.Reformulated.B.CountingPairs.Priv

private lemma cntGt {k : ℕ} (i : Fin k) :
    (∑ c : Fin k, if i < c then (1:ℤ) else 0) = (k:ℤ) - 1 - i := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun c : Fin k => i < c)) = Finset.Ioi i := by
    ext c; simp
  rw [this, Fin.card_Ioi]
  have := i.isLt
  push_cast [Nat.sub_sub, show 1 + (i:ℕ) ≤ k by omega]
  ring

private lemma cntLt {k : ℕ} (c : Fin k) :
    (∑ i : Fin k, if i < c then (1:ℤ) else 0) = (c:ℤ) := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin k => i < c)) = Finset.Iio c := by
    ext i; simp
  rw [this, Fin.card_Iio]

end UpperTheory.Reformulated.B.CountingPairs.Priv

open UpperTheory.Reformulated.B.CountingPairs.Priv in
theorem UpperTheory.Reformulated.B.CountingPairs.main :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by
  intro k l
  have h1 : ∀ c i : Fin k, (if i < c then l i - l c else (0:ℤ))
      = (if i < c then (1:ℤ) else 0) * l i - (if i < c then (1:ℤ) else 0) * l c := by
    intro c i; split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => (if i < c then (1:ℤ) else 0) * l i)]
  simp_rw [← Finset.sum_mul, cntGt, cntLt]
  unfold UpperTheory.Reformulated.B.CountingPairs.rhoPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
