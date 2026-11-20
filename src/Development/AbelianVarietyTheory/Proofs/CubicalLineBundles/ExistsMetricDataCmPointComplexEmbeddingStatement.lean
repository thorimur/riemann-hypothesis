import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetricDataCmPointComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_metricData_cmPoint_complexEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (σ : z.K →+* ℂ) (yσ : FrPt Xo c (CAt (σ.comp (algebraMap c.F z.K)))), FrMap (embAlg σ) z.y yσ → ∃ Hm : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) ℂ, Hm.PosDef ∧ z.LamL.n σ = Real.sqrt Hm.det.re ∧ (∀ j, ReciprocityTheory.MultiplicativeHeights.hq Hm (ReciprocityTheory.MultiplicativeHeights.embVec σ (z.U j)) ≤ (La * (z.ℓ j).n σ) ^ 2) ∧ IsMetric yσ (z.Tl.n σ ^ 2) (gramBlock z.e z.U Hm σ) := by
  first | exact @GlobalTheory.LamT.CMMetric.exists_isMetric | exact GlobalTheory.LamT.CMMetric.exists_isMetric | (intros; apply GlobalTheory.LamT.CMMetric.exists_isMetric <;> assumption)
