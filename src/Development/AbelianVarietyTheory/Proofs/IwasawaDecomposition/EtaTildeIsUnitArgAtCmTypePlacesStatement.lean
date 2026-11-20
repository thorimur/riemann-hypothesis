import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaTilde_isUnitArg_at_cmType_places : ∀ {R : Ranks} (H : Host R) (χ : HChar H.E), IsEtaT H χ → ∀ (h : Formalism.L2.NC.HC H.E), h.χ = (χ : Ideles H.E →* ℂˣ) → ∀ (g : R.Psi), h.IsUnitArg (H.emb (g : R.GG)) := by
  first | exact @GlobalTheory.EtaUnitArg.etaT_isUnitArg | exact GlobalTheory.EtaUnitArg.etaT_isUnitArg | (intros; apply GlobalTheory.EtaUnitArg.etaT_isUnitArg <;> assumption)
