import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WallSmallnessOfDegrees
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wall_smallness_of_degrees : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), 2 < D.R.f * (Y.N - 1) → Positive A → Squeeze A → Heights A → Degrees A → WallSmall A := by
  first | exact @GlobalTheory.Mean4.NearWall.wallSmall | exact GlobalTheory.Mean4.NearWall.wallSmall | (intros; apply GlobalTheory.Mean4.NearWall.wallSmall <;> assumption)
