import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace

private lemma isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range {ι : Type} [Finite ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] {W : Type*} [TopologicalSpace W] (g : ∀ i, Z i → W)
    (hg : ∀ i, Topology.IsClosedEmbedding (g i))
    (h : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j))) :
    Topology.IsClosedEmbedding (fun p : Σ i, Z i => g p.1 p.2) := by
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · exact continuous_sigma fun i => (hg i).continuous
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst hij
      obtain rfl := (hg i).injective hxy
      rfl
    · exact absurd hxy ((h hij).ne_of_mem ⟨x, rfl⟩ ⟨y, rfl⟩)
  · intro C hC
    have hC' : (fun p : Σ i, Z i => g p.1 p.2) '' C = ⋃ i, g i '' (_root_.Sigma.mk i ⁻¹' C) := by
      ext w
      simp
    rw [hC']
    exact isClosed_iUnion_of_finite fun i => (hg i).isClosedMap _ (hC.preimage continuous_sigmaMk)

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial in

theorem _root_.GlobalTheory.ProjSpace.isClosedImmersion_sigmaDesc {ι : Type} [Finite ι]
    {X : ι → Scheme.{0}} {Y : Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsClosedImmersion (f i))
    (h : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) :
    IsClosedImmersion (Sigma.desc f) := by
  have hsurj : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun i => (hf i).toSurjectiveOnStalks
  have key : ⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X = fun p => f p.1 p.2 := by
    funext ⟨i, x⟩
    rw [Function.comp_apply, AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hce : Topology.IsClosedEmbedding (Sigma.desc f) := by
    have e := isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range (fun i => ⇑(f i))
      (fun i => (hf i).isClosedEmbedding) h
    rw [← key] at e
    have hsplit : ⇑(Sigma.desc f) =
        (⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X) ∘ (AlgebraicGeometry.sigmaMk X).symm := by
      funext y
      simp
    rw [hsplit]
    exact e.comp (AlgebraicGeometry.sigmaMk X).symm.isClosedEmbedding
  haveI : IsPreimmersion (Sigma.desc f) := (isPreimmersion_iff _).2 ⟨hsurj, hce.isEmbedding⟩
  exact .of_isPreimmersion _ hce.isClosed_range

end GlobalTheory.ProjSpace
