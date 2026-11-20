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

theorem UpperTheory.Reformulated.B.Qf49.add_pow_nsmul :
    ∀ {Γ W : Type} [inst : Group Γ] [inst_1 : AddCommGroup W]
    (U : Subgroup Γ) (f : Γ → W),
    (∀ u ∈ U, ∀ v ∈ U, f (u * v) = f u + f v) → f (1 : Γ) = (0 : W) ∧ ∀ u ∈ U, ∀ (k : ℕ), f (u ^ k) = k • f u := by
  intro Γ W _ _ U f h
  have h1 : f 1 = 0 := by
    have h11 := h 1 U.one_mem 1 U.one_mem
    rw [one_mul] at h11
    exact left_eq_add.mp h11
  refine ⟨h1, fun u hu k => ?_⟩
  induction k with
  | zero => rw [pow_zero, zero_nsmul, h1]
  | succ k ih => rw [pow_succ, h _ (U.pow_mem hu k) u hu, ih, succ_nsmul]
