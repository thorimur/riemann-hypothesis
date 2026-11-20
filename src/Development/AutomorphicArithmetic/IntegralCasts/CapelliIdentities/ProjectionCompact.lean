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
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.ProjectionCompact.piK :
    {T κ : Type} →
      [inst : Fintype T] →
        [inst_1 : DecidableEq T] →
          [inst_2 : Fintype κ] → [inst_3 : DecidableEq κ] → (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ :=
  fun {T κ} _ _ _ _ =>
    { toFun := fun M => Matrix.of fun f g => ∏ t, M t (f t) (g t)
      map_one' := by
        ext f g
        simp only [Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
        by_cases h : f = g
        · subst h
          simp
        · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
          rw [if_neg h]
          exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
      map_mul' := fun M N => by
        ext f g
        simp only [Matrix.of_apply, Pi.mul_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun h _ => Finset.prod_mul_distrib }
