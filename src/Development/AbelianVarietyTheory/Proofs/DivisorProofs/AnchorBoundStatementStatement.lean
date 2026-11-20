import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchor_bound_statement : Anchor := by
  first | exact @GlobalTheory.CovTop.anchor_holds | exact GlobalTheory.CovTop.anchor_holds | (intros; apply GlobalTheory.CovTop.anchor_holds <;> assumption)
