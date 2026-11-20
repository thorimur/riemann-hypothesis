import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.Order.CompletePartialOrder
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

open scoped BigOperators

namespace GlobalTheory

theorem exists_limit_family_of_finite_coefficients (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩

end GlobalTheory
