import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralShellsVanishBeyondPeriodRamified
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.ShellLemma := by
  first | exact @GlobalTheory.ShellVan.shell_lemma | exact GlobalTheory.ShellVan.shell_lemma | (intros; apply GlobalTheory.ShellVan.shell_lemma <;> assumption)
