import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)
