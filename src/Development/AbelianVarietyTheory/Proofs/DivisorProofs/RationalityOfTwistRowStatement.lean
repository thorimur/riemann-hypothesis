import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfTwistRow
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_twist_row : TwAdm → RowAt → TieRat := by
  first | exact @GlobalTheory.BigOn.Exp.tieRat_of | exact GlobalTheory.BigOn.Exp.tieRat_of | (intros; apply GlobalTheory.BigOn.Exp.tieRat_of <;> assumption)
