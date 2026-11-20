import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SitePD

theorem pdPoly_flat_comp : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat →
    ((algebraMap B (pq B).P).comp i).Flat := by
  intro A B _ _ i hi
  have hfree : Module.Free B (pq B).P := Module.Free.of_basis (pq B).e
  have h2 : (algebraMap B (pq B).P).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  exact RingHom.Flat.comp hi h2

end GlobalTheory.CompanionTheory.SitePD
