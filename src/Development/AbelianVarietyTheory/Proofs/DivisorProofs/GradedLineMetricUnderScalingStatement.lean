import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineMetricUnderScaling
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_line_metric_under_scaling : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (s : ℝ), (VMetric.grLB fl i (H.scale s)).Isometric ((VMetric.grLB fl i H).shift (fun _ => -s / 2) fun _ => rfl) := by
  first | exact @GlobalTheory.GradedScale.grLB_scale_isometric | exact GlobalTheory.GradedScale.grLB_scale_isometric | (intros; apply GlobalTheory.GradedScale.grLB_scale_isometric <;> assumption)
