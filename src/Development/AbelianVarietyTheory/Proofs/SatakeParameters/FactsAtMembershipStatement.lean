import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FactsAtMembership
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.facts_at_membership : PrN → GlobalTheory.NRows.HypothesesX → SerN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => Facts (w.D Z) nch := by
  first | exact @GlobalTheory.NFacts.AtMemFacts.facts_atMem | exact GlobalTheory.NFacts.AtMemFacts.facts_atMem | (intros; apply GlobalTheory.NFacts.AtMemFacts.facts_atMem <;> assumption)
