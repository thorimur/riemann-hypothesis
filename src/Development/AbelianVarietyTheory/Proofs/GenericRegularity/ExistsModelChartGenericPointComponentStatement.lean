import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_modelChart_genericPoint_component : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  first | exact @GlobalTheory.GenericChart.exists_chart_genPt | exact GlobalTheory.GenericChart.exists_chart_genPt | (intros; apply GlobalTheory.GenericChart.exists_chart_genPt <;> assumption)
