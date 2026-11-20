import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arakelov_top_unique : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (t t' : ℝ), A.IsArTop t → A.IsArTop t' → t = t' := by
  first | exact @GlobalTheory.TrueGeo.ArUniq.isArTop_unique | exact GlobalTheory.TrueGeo.ArUniq.isArTop_unique | (intros; apply GlobalTheory.TrueGeo.ArUniq.isArTop_unique <;> assumption)
