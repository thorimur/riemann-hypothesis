import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_space_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.TupCovol := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | exact GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | (intros; apply GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol <;> assumption)
