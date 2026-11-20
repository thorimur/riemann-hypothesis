import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAtOfCh2Constant
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
theorem _root_.GlobalTheory.T.de_rham_at_of_ch2_constant : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.Ch2HodgeVanishes → ∀ r : ℝ, Ch2Const r → OnObj fun _ O _ _ _ _ => DRAt O.Y r := by
  first | exact @GlobalTheory.DeRhamValue.main | exact GlobalTheory.DeRhamValue.main | (intros; apply GlobalTheory.DeRhamValue.main <;> assumption)
