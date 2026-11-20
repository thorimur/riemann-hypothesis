import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_existence : CanEx := by
  first | exact @GlobalTheory.BigOn.Exp.canEx_holds | exact GlobalTheory.BigOn.Exp.canEx_holds | (intros; apply GlobalTheory.BigOn.Exp.canEx_holds <;> assumption)
