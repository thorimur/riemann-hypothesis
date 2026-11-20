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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

universe u_1 u_2

namespace GlobalTheory.ProdMapMulSingle

theorem prod_map_mulSingle_apply {ι : Type u_1} [DecidableEq ι] {M : ι → Type u_2}
    [(i : ι) → Monoid (M i)] (x : (i : ι) → M i) (l : List ι) (hl : List.Nodup l) (w : ι) :
    List.prod (List.map (fun (i : ι) ↦ Pi.mulSingle i (x i)) l) w
      = if w ∈ l then x w else (1 : M w) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl']
    by_cases h : w = a
    · subst h
      rw [if_neg ha, if_pos List.mem_cons_self, Pi.mulSingle_eq_same, mul_one]
    · rw [Pi.mulSingle_eq_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

end GlobalTheory.ProdMapMulSingle
