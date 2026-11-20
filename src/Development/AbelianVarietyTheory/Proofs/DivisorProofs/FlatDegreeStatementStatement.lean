import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_degree_statement : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → FlatDeg := by
  first | exact @GlobalTheory.CovTop.FlatDegProof.flatDeg | exact GlobalTheory.CovTop.FlatDegProof.flatDeg | (intros; apply GlobalTheory.CovTop.FlatDegProof.flatDeg <;> assumption)
