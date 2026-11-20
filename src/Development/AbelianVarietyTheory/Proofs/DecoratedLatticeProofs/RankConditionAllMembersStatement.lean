import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_condition_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @GlobalTheory.Fam.MemberCount.member_rankMu | exact GlobalTheory.Fam.MemberCount.member_rankMu | (intros; apply GlobalTheory.Fam.MemberCount.member_rankMu <;> assumption)
