import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompact
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_decomposition_of_compact : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f)) → GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  first | exact @GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | exact GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | (intros; apply GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact <;> assumption)
