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

universe u_1

namespace GlobalTheory.ProductOfFnSingle

theorem prod_ofFn_eq_single {M : Type u_1} [inst : Monoid M] {d : ℕ} (g : Fin d → M) (j : Fin d)
    (h : ∀ (i : Fin d), i ≠ j → g i = (1 : M)) : List.prod (List.ofFn g) = g j := by
  induction d with
  | zero => exact j.elim0
  | succ d ih =>
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have hrest : List.prod (List.ofFn fun i : Fin d => g i.succ) = 1 := by
        apply List.prod_eq_one
        intro x hx
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero i)
      rw [hrest, mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (fun e => hj e.symm), one_mul]
      exact ih (fun i => g i.succ) j' (fun i hi => h _ (fun e => hi (Fin.succ_injective _ e)))

end GlobalTheory.ProductOfFnSingle
