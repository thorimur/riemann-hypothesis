import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finsupp.WellFounded
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

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.gordan_dickson (σ : Type) [Finite σ] (S : Set (σ →₀ ℕ)) :
    ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, m ∈ S) ∧ ∀ n ∈ S, ∃ m ∈ μ, m ≤ n := by
  classical
  haveI := Fintype.ofFinite σ
  have hfin : {m : σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, fun n hn => ?_⟩
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

theorem UpperTheory.V.Alg.gordan :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X), ∃ g : Finset (σ →₀ ℕ), (∀ n ∈ g, n ≠ 0 ∧ Finsupp.weight wt n = 0) ∧
      (∀ n, Finsupp.weight wt n = 0 → n ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ))) ∧
      ∀ j, ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, Finsupp.weight wt m = j) ∧ ∀ n, Finsupp.weight wt n = j → ∃ m ∈ μ, m ≤ n := by
  intro σ _ X _ _ _ wt
  classical
  obtain ⟨g, hgS, hg⟩ := gordan_dickson σ {n | n ≠ 0 ∧ Finsupp.weight wt n = 0}
  refine ⟨g, hgS, ?_, fun j => ?_⟩
  · intro n
    induction n using WellFoundedLT.induction with
    | _ n ih =>
      intro hn
      by_cases h0 : n = 0
      · rw [h0]
        exact zero_mem _
      · obtain ⟨m, hm, hmn⟩ := hg n ⟨h0, hn⟩
        have hm' := hgS m hm
        have hsplit : n = m + (n - m) := (add_tsub_cancel_of_le hmn).symm
        have hw : Finsupp.weight wt (n - m) = 0 := by
          have h1 := hn
          rw [hsplit, map_add, hm'.2, zero_add] at h1
          exact h1
        have hlt : n - m < n := by
          refine lt_of_le_of_ne tsub_le_self fun h => hm'.1 ?_
          have h2 : m + (n - m) = n := add_tsub_cancel_of_le hmn
          rw [h] at h2
          simpa using h2
        rw [hsplit]
        exact add_mem (AddSubmonoid.subset_closure hm) (ih _ hlt hw)
  · obtain ⟨μ, hμS, hμ⟩ := gordan_dickson σ {n | Finsupp.weight wt n = j}
    exact ⟨μ, hμS, hμ⟩
