import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivLOneBoundFamily
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_deriv_L_one_bound_family : GlobalTheory.FunPr.Hypotheses₂ → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) := by
  first | exact @GlobalTheory.log_deriv_L_one_le_along_family | exact GlobalTheory.log_deriv_L_one_le_along_family | (intros; apply GlobalTheory.log_deriv_L_one_le_along_family <;> assumption)
