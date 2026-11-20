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

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem relIndex_ne_zero_of_isCompact_of_relOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (S K K' : Subgroup G),
      K' ≤ S → IsCompact (K' : Set G) →
      (∃ O : Set G, IsOpen O ∧ O ∩ (S : Set G) = (K : Set G)) → K.relIndex K' ≠ 0 := by
  intro G _ _ _ S K K' hK'S hK' ⟨O, hO, hOS⟩
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  have hopen : IsOpen ((K.subgroupOf K' : Subgroup K') : Set K') := by
    have hset : ((K.subgroupOf K' : Subgroup K') : Set K') = Subtype.val ⁻¹' O := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      constructor
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := by rw [hOS]; exact hx
        exact this.1
      · intro hx
        have : (x : G) ∈ O ∩ (S : Set G) := ⟨hx, hK'S x.2⟩
        rw [hOS] at this
        exact this
    rw [hset]
    exact hO.preimage continuous_subtype_val
  have := (K.subgroupOf K').quotient_finite_of_isOpen hopen
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.Ar.Cmp
