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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf

noncomputable def UpperTheory.Reformulated.B.PadicComplexIntegerSubring.intSub :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] := fun p _ =>
  { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
    mul_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      rw [norm_mul]
      exact mul_le_one₀ ha (norm_nonneg b) hb
    one_mem' := by
      simp only [Set.mem_setOf_eq, norm_one, le_refl]
    add_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
    zero_mem' := by
      simp only [Set.mem_setOf_eq, norm_zero, zero_le_one]
    neg_mem' := fun {a} ha => by
      simp only [Set.mem_setOf_eq] at ha ⊢
      rwa [norm_neg] }
