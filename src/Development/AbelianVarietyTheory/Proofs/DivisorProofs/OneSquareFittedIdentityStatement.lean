import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_square_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → (Lf (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) → OneSqSt → OneSq @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.oneSq_tie | exact GlobalTheory.BigTop.Fun.oneSq_tie | (intros; apply GlobalTheory.BigTop.Fun.oneSq_tie <;> assumption)
