import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_irreducible_central_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  first | exact @GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | exact GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | (intros; apply GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar <;> assumption)
