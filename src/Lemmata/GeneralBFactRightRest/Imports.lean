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

universe u_1 u_2

namespace Bl.general_b_fact_right_rest

private theorem aux {α : Type u_1} {β : Type u_2} (f : α → β) (t : Multiset α) :
    ∀ s : Multiset β, s ≤ t.map f → ∃ u : Multiset α, u ≤ t ∧ u.map f = s := by
  induction t using Multiset.induction_on with
  | empty =>
    intro s hs
    rw [Multiset.map_zero, Multiset.le_zero] at hs
    exact ⟨0, le_refl _, by rw [Multiset.map_zero, hs]⟩
  | cons a t ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases h : f a ∈ s
    · obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem h
      rw [Multiset.cons_le_cons_iff] at hs
      obtain ⟨u, hu, hmap⟩ := ih s' hs
      exact ⟨a ::ₘ u, (Multiset.cons_le_cons_iff a).mpr hu, by rw [Multiset.map_cons, hmap]⟩
    · obtain ⟨u, hu, hmap⟩ := ih s ((Multiset.le_cons_of_notMem h).mp hs)
      exact ⟨u, hu.trans (Multiset.le_cons_self t a), hmap⟩

theorem goal1 :
  ∀ {α : Type u_1} {β : Type u_2} [DecidableEq.{u_2 + 1} β] (f : α → β) (t : Multiset.{u_1} α) (s : Multiset.{u_2} β),
  LE.le.{u_2} s (Multiset.map.{u_2, u_1} f t) →
    Exists.{u_1 + 1} fun (u : Multiset.{u_1} α) ↦ And (LE.le.{u_1} u t) (Eq.{u_2 + 1} (Multiset.map.{u_2, u_1} f u) s) := by
  intro α β _ f t s h
  exact aux f t s h

end Bl.general_b_fact_right_rest
