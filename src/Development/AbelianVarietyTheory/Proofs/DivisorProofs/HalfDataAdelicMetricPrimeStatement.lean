import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfDataAdelicMetricPrime
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.half_data_adelic_metric_prime : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    HalfDataC (fun k : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
      (wholeSym (Function.update (ArIn.ind Sx) p true) (some R)
        (Sum.inl k : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)))) p := by
  first | exact @GlobalTheory.HalfGeo.halfData_whole | exact GlobalTheory.HalfGeo.halfData_whole | (intros; apply GlobalTheory.HalfGeo.halfData_whole <;> assumption)
