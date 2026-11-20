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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open Polynomial

namespace GlobalTheory

theorem exists_primitive_element_of_isAlgebraic_fin (K C : Type) [Field K] [CharZero K]
    [Field C] [Algebra K C] (m : ℕ) (a : Fin m → C) (ha : ∀ j, IsAlgebraic K (a j)) :
    ∃ α : C, IsAlgebraic K α ∧ ∀ j, a j ∈ IntermediateField.adjoin K {α} := by
  classical
  let E := IntermediateField.adjoin K (Set.range a)
  haveI : FiniteDimensional K E := by
    haveI : Finite (Set.range a) := Set.finite_range a
    exact IntermediateField.finiteDimensional_adjoin (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact (ha j).isIntegral)
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  have hmap := congrArg (IntermediateField.map E.val) hβ
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  refine ⟨E.val β, ((Algebra.IsIntegral.isIntegral (R := K) β).map E.val).isAlgebraic, ?_⟩
  intro j
  rw [hmap]
  rw [IntermediateField.mem_map]
  exact ⟨⟨a j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩, trivial, rfl⟩

end GlobalTheory
