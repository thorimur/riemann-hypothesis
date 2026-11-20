import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentity
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → DenSum → Den @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.den_tie | exact GlobalTheory.BigTop.Fun.den_tie | (intros; apply GlobalTheory.BigTop.Fun.den_tie <;> assumption)
