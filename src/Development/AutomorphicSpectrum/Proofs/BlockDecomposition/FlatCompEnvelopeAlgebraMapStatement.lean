import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCompEnvelopeAlgebraMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_comp_envelope_algebraMap : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat → ((algebraMap B (pq B).P).comp i).Flat := by
  first | exact @GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | exact GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp | (intros; apply GlobalTheory.CompanionTheory.SitePD.pdPoly_flat_comp <;> assumption)
