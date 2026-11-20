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

namespace Bl.general_b_fact_upper_ter_form

private lemma aux {p : Nat} [Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : Real}
    (hC : 0 ≤ C) (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a t)
    · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset.{0} ι) (g : ι → PadicAlgCl p) {C : Real},
  LE.le.{0} 0 C →
    (∀ (j : ι), Membership.mem.{0, 0} s j → LE.le.{0} (Norm.norm.{0} (g j)) C) →
      LE.le.{0} (Norm.norm.{0} (Finset.sum.{0, 0} s fun (j : ι) ↦ g j)) C := by
  intro p _ ι s g C hC h
  exact aux s g hC h

end Bl.general_b_fact_upper_ter_form
