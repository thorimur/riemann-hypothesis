import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι], ∃ f ∈ schwartzBruhatPi F ι, HasCompactSupport f ∧ f 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero <;> assumption)
