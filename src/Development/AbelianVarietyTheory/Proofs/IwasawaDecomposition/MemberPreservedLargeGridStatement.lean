import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberPreservedLargeGrid
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.member_preserved_large_grid : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A → MemberE (prmR N S Γ).s → MemberE (prmR (NEa hL N A) S Γ).s := by
  first | exact @GlobalTheory.Mem.LiteralAutomorphy.memberE_prmR_NEa | exact GlobalTheory.Mem.LiteralAutomorphy.memberE_prmR_NEa | (intros; apply GlobalTheory.Mem.LiteralAutomorphy.memberE_prmR_NEa <;> assumption)
