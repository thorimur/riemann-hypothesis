import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentPicardGroup
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_descent_picard_group : GlobalTheory.EtC.DivisorPicardCompatibility := by
  first | (exact @GlobalTheory.EtC.b6pic_holds) | (exact GlobalTheory.EtC.b6pic_holds) | (intros; apply GlobalTheory.EtC.b6pic_holds <;> assumption)
