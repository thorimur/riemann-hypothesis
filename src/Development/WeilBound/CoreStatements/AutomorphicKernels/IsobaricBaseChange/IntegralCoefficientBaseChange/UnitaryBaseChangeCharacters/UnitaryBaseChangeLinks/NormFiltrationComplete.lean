import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFiltrationComplete
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_filtration_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  first | exact @GlobalTheory.NormEq.filtrationComplete_filt | exact GlobalTheory.NormEq.filtrationComplete_filt | (intros; apply GlobalTheory.NormEq.filtrationComplete_filt <;> assumption)
