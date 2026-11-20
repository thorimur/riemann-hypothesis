import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

namespace SupNormSqLeSumNormSq

private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)

end SupNormSqLeSumNormSq

theorem UpperTheory.Reformulated.B.Yhb3.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
