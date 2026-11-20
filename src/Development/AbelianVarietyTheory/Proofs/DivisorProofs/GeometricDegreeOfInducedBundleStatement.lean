import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeOfInducedBundle
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_degree_of_induced_bundle : GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (P : TrueGeo.Model Y) (L : HermLB P.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced P L k cf → gdeg L Y.dim = (Module.finrank ℤ (𝓞 F) : ℝ) * (((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ)) ^ Y.dim * A.deg := by
  first | exact @GlobalTheory.ReadModel.gdeg_induced | exact GlobalTheory.ReadModel.gdeg_induced | (intros; apply GlobalTheory.ReadModel.gdeg_induced <;> assumption)
