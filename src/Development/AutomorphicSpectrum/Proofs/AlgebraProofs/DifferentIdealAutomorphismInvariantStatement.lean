import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_ideal_automorphism_invariant : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff | exact GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff <;> assumption)
