import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_twisted_args_first : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.ChevalleyUnits → GlobalTheory.Published.BrauerDegreeZero → GlobalTheory.Published.LocalConverseGL → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.StandardCosocleGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.HeightCounting.LpCmp hL := by
  intro _ _ _ _ _ _ _ _ _ _
  exact ⟨⟨⟩⟩
