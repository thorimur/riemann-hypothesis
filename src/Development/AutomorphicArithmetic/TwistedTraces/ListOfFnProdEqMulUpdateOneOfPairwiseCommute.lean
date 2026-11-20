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
open scoped BigOperators

theorem UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute :
    ∀ (M : Type) [Monoid M] (r : ℕ) (a : Fin r → M), (∀ i j, i ≠ j → Commute (a i) (a j)) → ∀ i, (List.ofFn a).prod = a i * (List.ofFn (Function.update a i 1)).prod ∧ ∀ m : M, (∀ j, j ≠ i → Commute m (a j)) → Commute m (List.ofFn (Function.update a i 1)).prod := by
  intro M _ r a h i
  refine ⟨?_, ?_⟩
  · induction r with
    | zero => exact i.elim0
    | succ r ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · have h1 : (fun j : Fin r => Function.update a 0 1 j.succ) = fun j => a j.succ := by
          funext j
          rw [Function.update_of_ne (Fin.succ_ne_zero j)]
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_self, one_mul]
      · have h1 : (fun j : Fin r => Function.update a k.succ 1 j.succ)
            = Function.update (fun j : Fin r => a j.succ) k 1 := by
          funext j
          by_cases hj : j = k
          · subst hj
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hj,
              Function.update_of_ne (fun e => hj (Fin.succ_injective _ e))]
        have h2 := ih (fun j : Fin r => a j.succ)
          (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e))) k
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_of_ne (Fin.succ_ne_zero k).symm, h2, ← mul_assoc, ← mul_assoc,
          (h 0 k.succ (Fin.succ_ne_zero k).symm).eq]
  · intro m hm
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact Commute.one_right m
    · rw [Function.update_of_ne hj]
      exact hm j hj
