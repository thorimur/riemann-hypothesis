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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
