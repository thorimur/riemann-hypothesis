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

namespace GlobalTheory

theorem image_finite_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  intro G Q _ _ ρ J H hH hρ
  classical
  haveI := hH
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  apply (Set.finite_range (fun q : G ⧸ H =>
    if h : ∃ g ∈ J, (g : G ⧸ H) = q then ρ h.choose else 1)).subset
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨(g : G ⧸ H), ?_⟩
  have hex : ∃ g' ∈ J, (g' : G ⧸ H) = g := ⟨g, hg, rfl⟩
  dsimp only
  rw [dif_pos hex]
  obtain ⟨hJ, hq⟩ := hex.choose_spec
  have hmem : (hex.choose)⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
  have h1 := hρ _ (J.mul_mem (J.inv_mem hJ) hg) hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end GlobalTheory
