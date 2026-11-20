import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bound_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → ThbSt → Thb @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.thb_tie | exact GlobalTheory.BigTop.Fun.thb_tie | (intros; apply GlobalTheory.BigTop.Fun.thb_tie <;> assumption)
