import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem _root_.GlobalTheory.KeyTf.exists_finiteType_subring_adjoin :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (F : Finset S), Algebra.FiniteType ℤ R₀ →
      ∃ R₁ : Subring S, R₀ ≤ R₁ ∧ (F : Set S) ⊆ R₁ ∧ Algebra.FiniteType ℤ R₁ := by
  intro S _ R₀ F hR₀
  classical
  obtain ⟨s, hs⟩ := hR₀.out
  let T : Finset S := s.image (Subtype.val) ∪ F
  refine ⟨(Algebra.adjoin ℤ (T : Set S)).toSubring, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : R₀) ∈ Algebra.adjoin ℤ (s : Set R₀) := hs ▸ Algebra.mem_top
    have h2 : x ∈ (Algebra.adjoin ℤ (s : Set R₀)).map R₀.subtype.toIntAlgHom :=
      Subalgebra.mem_map.2 ⟨_, hmem, rfl⟩
    rw [← Algebra.adjoin_image] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨T, rfl⟩

end GlobalTheory.KeyTf
