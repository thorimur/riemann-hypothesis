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
import Std.Tactic.BVDecide.Normalize.Prop

theorem UpperTheory.Reformulated.B.Qh68.reps.{u_1} :
    ∀ {α : Type u_1} (r : α → α → Prop),
    Equivalence r → ∀ (A : Finset α), ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t := by
  intro α r hr A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T, hTs, hinj, hcov⟩ := ih
    by_cases h : ∃ t ∈ T, r a t
    · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h
      · exact hcov b hb
    · refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · intro t ht t' ht' htt
        rcases Finset.mem_insert.mp ht with h1 | h1
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · rw [h1, h2]
          · exact absurd ⟨t', h2, h1 ▸ htt⟩ h
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · exact absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h
          · exact hinj t h1 t' h2 htt
      · intro b hb
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact ⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩
        · obtain ⟨t, ht, hbt⟩ := hcov b h1
          exact ⟨t, Finset.mem_insert_of_mem ht, hbt⟩
