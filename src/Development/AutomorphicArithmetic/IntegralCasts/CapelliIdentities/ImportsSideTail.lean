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

theorem UpperTheory.Reformulated.B.Ylb7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {C : Set G},
      IsCompact C →
        ∀ {n : Set (G × G)}, IsOpen n → (∀ c ∈ C, (c, (1 : G)) ∈ n) → ∃ O ∈ nhds (1 : G), ∀ c ∈ C, ∀ u ∈ O, (c, u) ∈ n := by
  intro G _ _ C hC n hn h
  have hsub : C ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨c, u⟩ ⟨hc, hu⟩
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    exact h c hc
  obtain ⟨U, V, _, hV, _, hV1, hUV⟩ := generalized_tube_lemma hC isCompact_singleton hn hsub
  refine ⟨V, hV.mem_nhds (hV1 rfl), ?_⟩
  intro c hc u hu
  exact hUV ⟨‹C ⊆ U› hc, hu⟩
