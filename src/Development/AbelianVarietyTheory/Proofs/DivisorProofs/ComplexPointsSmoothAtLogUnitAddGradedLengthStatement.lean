import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLength
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  first | exact @GlobalTheory.ChernCalc.cInfAt_logUnit_grD | exact GlobalTheory.ChernCalc.cInfAt_logUnit_grD | (intros; apply GlobalTheory.ChernCalc.cInfAt_logUnit_grD <;> assumption)
