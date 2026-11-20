import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_data_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N N' : ℝ) (Gr Gr' : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), IsMetric y N Gr → IsMetric y N' Gr' → N = N' ∧ Gr = Gr' := by
  first | exact @GlobalTheory.LamT.MetUniq.isMetric_unique | exact GlobalTheory.LamT.MetUniq.isMetric_unique | (intros; apply GlobalTheory.LamT.MetUniq.isMetric_unique <;> assumption)
