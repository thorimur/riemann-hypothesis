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

namespace GlobalTheory.IntegerShiftSingle

universe u_1 u_2 u_3

theorem shift_single_int {ι : Type u_1} {R : Type u_2} {E : Type u_3} [DecidableEq ι] [Ring R]
    {F : (ι → R) → E} (h : ∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x)
    (i : ι) (k : ℤ) : ∀ x : ι → R, F (x + Pi.single i ((k : ℤ) : R)) = F x := by
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have : x + Pi.single i (((m : ℤ) + 1 : ℤ) : R) = (x + Pi.single i ((m : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [Int.cast_add, Int.cast_one, Pi.single_add, add_assoc]
    rw [this, h, ih]
  | pred m ih =>
    intro x
    have : x + Pi.single i ((-(m : ℤ) : ℤ) : R) = (x + Pi.single i ((-(m : ℤ) - 1 : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [add_assoc, ← Pi.single_add]
      congr 2
      push_cast
      first | rfl | ring | abel | simp
    rw [← ih x, this, h]

theorem main {ι : Type u_1} {R : Type u_2} {E : Type u_3} [Fintype ι] [inst : DecidableEq ι] [inst_1 : Ring R]
    {F : (ι → R) → E} : (∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x) →
    ∀ (n : ι → ℤ) (x : ι → R), F (x + fun (i : ι) ↦ (↑(n i) : R)) = F x := by
  intro h n x
  have key : ∀ s : Finset ι, ∀ y : ι → R, F (y + ∑ i ∈ s, Pi.single i ((n i : ℤ) : R)) = F y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc, ih, shift_single_int h]
  have hsum : (fun i : ι => ((n i : ℤ) : R)) = ∑ i ∈ Finset.univ, Pi.single i ((n i : ℤ) : R) := by
    rw [Finset.univ_sum_single]
  rw [hsum]
  exact key Finset.univ x

end GlobalTheory.IntegerShiftSingle
