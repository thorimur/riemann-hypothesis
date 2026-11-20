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

noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
