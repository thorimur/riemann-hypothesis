import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_unitary_entries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) RL.DifferentialCondition := by
  first | exact @GlobalTheory.Fc.RL.at_row_df | exact GlobalTheory.Fc.RL.at_row_df | (intros; apply GlobalTheory.Fc.RL.at_row_df <;> assumption)
