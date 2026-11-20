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

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_diag :
    ∀ (F : Filter ℕ), F ≤ atTop → ∀ P : ℕ → ℕ → Prop, (∀ j, ∀ᶠ N in F, P j N) →
      ∃ ν : ℕ → ℕ, Tendsto ν F atTop ∧ ∀ᶠ N in F, ∀ j ≤ ν N, P j N := by
  classical
  intro F hF P hP
  have hall : ∀ j, ∀ᶠ N in F, ∀ i ≤ j, P i N := fun j =>
    (Filter.eventually_all_finite (Set.finite_Iic j)).2 (fun i _ => hP i)
  refine ⟨fun N => Nat.findGreatest (fun j => ∀ i ≤ j, P i N) N, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro j
    filter_upwards [hall j, hF (eventually_ge_atTop j)] with N h1 h2
    exact Nat.le_findGreatest (P := fun j => ∀ i ≤ j, P i N) h2 h1
  · filter_upwards [hall 0] with N h1
    exact Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, P i N) (Nat.zero_le N) h1
