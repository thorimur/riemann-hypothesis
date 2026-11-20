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
import Std.Tactic.BVDecide.Normalize.Prop

namespace Bl.FirstBlockLemmaL

theorem goal1 :
  ∀ (ℓ : Nat) [Fact (Nat.Prime ℓ)] (s : Multiset.{0} Nat),
  (∀ (x : Nat), Membership.mem.{0, 0} s x → Ne.{1} x 0) →
    Eq.{1} (padicValNat ℓ (Multiset.prod.{0} s)) (Multiset.sum.{0} (Multiset.map.{0, 0} (padicValNat ℓ) s)) := by
  intro ℓ _ s hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ≠ 0 := hs a (by simp)
    have ht' : ∀ x, x ∈ t → x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have ht : t.prod ≠ 0 := by
      rw [Ne, Multiset.prod_eq_zero_iff]
      intro h
      exact ht' 0 h rfl
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, padicValNat.mul ha ht, ih ht']

end Bl.FirstBlockLemmaL
