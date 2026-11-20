import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FullConclusionOfInputs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_conclusion_of_inputs : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → Core D := by
  first | exact @GlobalTheory.CoreFacts.main | exact GlobalTheory.CoreFacts.main | (intros; apply GlobalTheory.CoreFacts.main <;> assumption)
