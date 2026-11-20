import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_atlas_snc_section : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | exact GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Adapt.exists_adaptedAtlas <;> assumption)
