import Mathlib.Topology.Algebra.ClopenNhdofOne
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

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
      (Z : Subgroup G) (P : G → Prop), (∀ V : Subgroup Z, V.FiniteIndex → ∀ σ : Z, ∃ g ∈ V, P (σ * g : Z)) →
      ∀ U : Set G, IsOpen U → (U ∩ (Z : Set G)).Nonempty → ∃ σ ∈ U ∩ (Z : Set G), P σ := by
  intro G _ _ _ _ _ Z P h U hU hne
  obtain ⟨σ, hσU, hσZ⟩ := hne
  have hW : IsOpen ((fun x : G => σ * x) ⁻¹' U) := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ ((fun x : G => σ * x) ⁻¹' U) := by simpa using hσU
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  have hfi : (N.toSubgroup).FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hP⟩ := h (N.toSubgroup.subgroupOf Z) inferInstance ⟨σ, hσZ⟩
  refine ⟨_, ⟨?_, ((⟨σ, hσZ⟩ : Z) * g).2⟩, hP⟩
  exact hN (show (g : G) ∈ N.toSubgroup from hg)
