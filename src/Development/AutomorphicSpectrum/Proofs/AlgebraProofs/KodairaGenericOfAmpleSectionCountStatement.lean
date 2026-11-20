import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count <;> assumption)
