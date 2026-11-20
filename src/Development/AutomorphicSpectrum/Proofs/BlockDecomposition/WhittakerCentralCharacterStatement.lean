import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_central_character : Ad3.SchwartzSpaceL2.SCen := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerCentral.sCen | exact GlobalTheory.CompanionTheory.WhittakerCentral.sCen | (intros; apply GlobalTheory.CompanionTheory.WhittakerCentral.sCen <;> assumption)
