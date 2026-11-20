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
import Std.Tactic.BVDecide.Normalize.Prop

theorem UpperTheory.Reformulated.B.Yra3.main :
    ∀ {R L : Type} [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) →
        ∀ (s : Finset L), ∃ (b : R), IsUnit ((φ : R → L) b) ∧ ∀ z ∈ s, z * (φ : R → L) b ∈ Set.range (⇑φ : R → L) := by
  intro R L _ _ φ h s
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert z s _ ih =>
    obtain ⟨b0, hb0, hs⟩ := ih
    obtain ⟨a, b, hb, hz⟩ := h z
    refine ⟨b0 * b, by rw [map_mul]; exact hb0.mul hb, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · refine ⟨a * b0, ?_⟩
      rw [map_mul, map_mul, ← hz]; ring
    · obtain ⟨c, hc⟩ := hs w hw
      refine ⟨c * b, ?_⟩
      rw [map_mul, map_mul, hc]; ring
