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

theorem UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main.{u_3} :
    ∀ {n : ℕ} {M : Type u_3} [inst : AddCommMonoid M]
    (F : Fin n → Fin n → M),
    ∑ a : Fin n, ∑ b : Fin n, F a b =
      ∑ a : Fin n, F a a + ∑ a : Fin n, ∑ b : Fin n, if a < b then F a b + F b a else (0 : M) := by
  intro n M _ F
  have h1 : ∀ a b : Fin n, F a b = (if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hd : ∀ a : Fin n, (∑ b : Fin n, if a = b then F a b else 0) = F a a := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  have hc : (∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0)
      = ∑ a : Fin n, ∑ b : Fin n, if a < b then F b a else 0 := by
    rw [Finset.sum_comm]
  calc ∑ a : Fin n, ∑ b : Fin n, F a b
      = ∑ a : Fin n, ∑ b : Fin n, ((if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
    _ = ∑ a : Fin n, F a a + ((∑ a : Fin n, ∑ b : Fin n, if a < b then F a b else 0)
        + ∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) := by
        simp only [Finset.sum_add_distrib, hd]
    _ = _ := by
        rw [hc, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
