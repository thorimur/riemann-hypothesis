import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelic
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norms_of_nonzero_adelic : ∀ (k : Type) [Field k] [NumberField k] (x : k), x ≠ 0 → (LogNorms.ofElt x).IsAdelic := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | exact GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.isAdelic_ofElt <;> assumption)
