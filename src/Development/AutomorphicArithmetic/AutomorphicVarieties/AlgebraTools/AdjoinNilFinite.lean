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

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.adjoin_nil_finite :
    ∀ {A G : Type} [CommRing A] [IsLocalRing A] [CommRing G] [Algebra A G] [Nontrivial G] (P : Submodule A G), P.FG → (∀ y ∈ P, ∃ a : A, IsNilpotent (y - algebraMap A G a)) → Module.Finite A (Algebra.adjoin A (P : Set G)) ∧ IsLocalRing (Algebra.adjoin A (P : Set G)) ∧ ∀ y ∈ Algebra.adjoin A (P : Set G), ∃ a : A, IsNilpotent (y - algebraMap A G a) := by
  intro A G _ _ _ _ _ P hP hnil
  let N : Subalgebra A G :=
    { carrier := {y | ∃ a : A, IsNilpotent (y - algebraMap A G a)}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        have e : x * y - algebraMap A G (a * b) =
            (x - algebraMap A G a) * y + algebraMap A G a * (y - algebraMap A G b) := by
          rw [map_mul]; ring
        rw [e]
        obtain ⟨k, hk⟩ := ha
        obtain ⟨m, hm⟩ := hb
        exact (Commute.all _ _).isNilpotent_add ⟨k, by rw [mul_pow, hk, zero_mul]⟩
          ⟨m, by rw [mul_pow, hm, mul_zero]⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have e : x + y - algebraMap A G (a + b) =
            (x - algebraMap A G a) + (y - algebraMap A G b) := by
          rw [map_add]; ring
        rw [e]
        exact (Commute.all _ _).isNilpotent_add ha hb
      algebraMap_mem' := fun r => ⟨r, by simp⟩ }
  have hS : Algebra.adjoin A (P : Set G) ≤ N := Algebra.adjoin_le (fun y hy => hnil y hy)
  have hint : ∀ y, (∃ a : A, IsNilpotent (y - algebraMap A G a)) → IsIntegral A y := by
    rintro y ⟨a, k, hk⟩
    have hn : IsIntegral A (y - algebraMap A G a) :=
      ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
    have := hn.add (isIntegral_algebraMap (x := a))
    simpa using this
  refine ⟨?_, ?_, fun y hy => hS hy⟩
  · obtain ⟨s, hs⟩ := hP
    rw [← hs, Algebra.adjoin_span]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun y hy => hint y (hnil y (hs ▸ Submodule.subset_span hy)))
  · apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro y
    obtain ⟨a, ha⟩ := hS y.2
    let n : Algebra.adjoin A (P : Set G) :=
      ⟨(y : G) - algebraMap A G a, Subalgebra.sub_mem _ y.2 (Subalgebra.algebraMap_mem _ a)⟩
    have hn : IsNilpotent n := by
      obtain ⟨k, hk⟩ := ha
      exact ⟨k, Subtype.ext (by simpa [n] using hk)⟩
    have hy : y = algebraMap A _ a + n := Subtype.ext (by simp [n])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
    · left
      rw [hy, add_comm]
      exact hn.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
    · right
      have e : 1 - y = algebraMap A _ (1 - a) + (-n) := by
        rw [hy, map_sub, map_one]; ring
      rw [e, add_comm]
      exact hn.neg.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
