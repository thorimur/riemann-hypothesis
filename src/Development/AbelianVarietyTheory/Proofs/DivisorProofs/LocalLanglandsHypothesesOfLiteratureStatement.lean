import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiterature
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_hypotheses_of_literature : LitNE → GlobalTheory.NRows.HypothesesX → HypE ∧ PrN ∧ SerN ∧ ∃ hL : GlobalTheory.Published.LocalLanglandsGL, HypN hL := by
  first | exact @GlobalTheory.MemberClose.hyps_of_litNE | exact GlobalTheory.MemberClose.hyps_of_litNE | (intros; apply GlobalTheory.MemberClose.hyps_of_litNE <;> assumption)
