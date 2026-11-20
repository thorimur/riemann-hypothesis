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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat
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
import Mathlib.Topology.Sheaves.Presheaf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
open IsLocalRing

theorem maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre :
    ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O]
      [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat →
      IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  intro O' O _ _ _ _ _ σ hloc hflat hart g hg
  letI := σ.toAlgebra
  haveI : Module.Flat O' O := hflat
  haveI : Algebra.HasGoingDown O' O := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap O' O) := hloc
  haveI : IsLocalHom σ := hloc
  set I : Ideal O := (maximalIdeal O').map σ with hI
  have hIle : I ≤ maximalIdeal O := IsLocalRing.map_maximalIdeal_le _
  haveI : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top hIle)
  haveI : IsLocalRing (O ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (O ⧸ I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hle => ?_⟩
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le (maximalIdeal.isMaximal _).ne_top
      hle).ge
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal O') (maximalIdeal O)
  have hIalg : (maximalIdeal O').map (algebraMap O' O) = I := rfl
  rw [hIalg, hmap, hF, add_zero] at H
  have hdim : ((maximalIdeal O').spanFinrank : WithBot ℕ∞) = g := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, ← maximalIdeal_height_eq_ringKrullDim, ← H,
      maximalIdeal_height_eq_ringKrullDim, hg]
  have hg' : (maximalIdeal O').spanFinrank = g := by exact_mod_cast hdim
  have hfg : (maximalIdeal O').FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hg'] at htcard
  let u : Fin g → O' := fun i => (t.equivFin.symm (Fin.cast htcard.symm i) : O')
  have hu : Set.range u = (t : Set O') := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm _).2
    · intro hx; exact ⟨Fin.cast htcard (t.equivFin ⟨x, hx⟩), by simp [u]⟩
  refine ⟨fun i => σ (u i), ?_⟩
  rw [hI, ← htspan, Ideal.map_span, ← hu, ← Set.range_comp]
  rfl

end GlobalTheory
