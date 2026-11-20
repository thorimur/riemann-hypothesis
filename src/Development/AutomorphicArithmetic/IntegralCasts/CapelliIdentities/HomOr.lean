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

namespace UpperTheory.Reformulated.B.Qk44

theorem hom_or {Γ C : Type} [Group Γ] [CommGroup C] (I : Subgroup Γ) (f g h : Γ →* C)
    (H : ∀ s ∈ I, f s = g s ∨ f s = h s) :
    (∀ s ∈ I, f s = g s) ∨ ∀ s ∈ I, f s = h s := by
  by_cases hg : ∀ s ∈ I, f s = g s
  · exact Or.inl hg
  · right
    obtain ⟨a, ha⟩ := not_forall.mp hg
    obtain ⟨haI, hne⟩ := Classical.not_imp.mp ha
    have hah : f a = h a := (H a haI).resolve_left hne
    intro b hbI
    rcases H b hbI with hb | hb
    · rcases H (a * b) (I.mul_mem haI hbI) with hab | hab
      · rw [map_mul, map_mul, hb] at hab
        exact absurd (mul_right_cancel hab) hne
      · rw [map_mul, map_mul, hah] at hab
        exact mul_left_cancel hab
    · exact hb

end UpperTheory.Reformulated.B.Qk44
