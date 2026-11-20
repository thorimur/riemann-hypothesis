import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtWholeSymbolReindexed
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_at_whole_symbol_reindexed : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core →
    ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ c : O.s.Comp,
    ∃ e : Fin (2 * (D.R.f * O.N)) ≃ Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N),
      FlagAt (fun i => adlOf (O.Φ.C c) (O.met.hm c)
        (wholeSym (Function.update (ArIn.ind Sx) p true) (some R) (e i))) p := by
  first | exact @GlobalTheory.TrivFlag.flagAt_wholeSym | exact GlobalTheory.TrivFlag.flagAt_wholeSym | (intros; apply GlobalTheory.TrivFlag.flagAt_wholeSym <;> assumption)
