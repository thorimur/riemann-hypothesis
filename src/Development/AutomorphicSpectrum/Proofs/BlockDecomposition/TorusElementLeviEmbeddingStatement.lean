import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusElementLeviEmbedding
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_element_levi_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (t : ℝ),
  aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | exact GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | (intros; apply GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev <;> assumption)
