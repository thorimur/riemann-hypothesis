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
import Mathlib.Tactic.ENatToNat
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
open Polynomial
open Classical

namespace GlobalTheory

theorem multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro K _ s ρ A B hρ hB hAB hball
  set S := s.toFinset.powerset.filter
    (fun Z : Finset K => ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hZS
  obtain ⟨hZsub, hZsep⟩ := hZS
  have hZs : ∀ W ∈ Z, W ∈ s := fun W hW => Multiset.mem_toFinset.mp (hZsub hW)
  have hcov : ∀ z ∈ s, ∃ W ∈ Z, ‖z - W‖ ≤ ρ := by
    intro z hz
    by_contra h
    push_neg at h
    have hzZ : z ∉ Z := by
      intro hzZ
      have := h z hzZ
      simp at this
      linarith
    have hmem : insert z Z ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (Multiset.mem_toFinset.mpr hz) hZsub, ?_⟩
      intro W hW W' hW' hne
      rw [Finset.mem_insert] at hW hW'
      rcases hW with rfl | hW <;> rcases hW' with rfl | hW'
      · exact absurd rfl hne
      · exact h W' hW'
      · rw [norm_sub_rev]; exact h W hW
      · exact hZsep W hW W' hW' hne
    have := hZmax _ hmem
    rw [Finset.card_insert_of_notMem hzZ] at this
    omega
  have hle : s ≤ ∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ) := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    by_cases ha : a ∈ s
    · obtain ⟨W, hW, hd⟩ := hcov a ha
      calc Multiset.count a s = Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
            rw [Multiset.count_filter_of_pos (p := fun z => ‖z - W‖ ≤ ρ) hd]
        _ ≤ _ := Finset.single_le_sum
            (f := fun W => Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)))
            (fun _ _ => Nat.zero_le _) hW
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  have hcard : Multiset.card s ≤ Z.card * B := by
    calc Multiset.card s ≤ Multiset.card (∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ)) :=
          Multiset.card_le_card hle
      _ = ∑ W ∈ Z, Multiset.card (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
          simp [map_sum]
      _ ≤ ∑ W ∈ Z, B := Finset.sum_le_sum fun W hW => hball W (hZs W hW)
      _ = Z.card * B := by simp
  exact ⟨Z, Nat.le_of_mul_le_mul_right (hAB.trans hcard) hB, hZs, hZsep⟩

end GlobalTheory
