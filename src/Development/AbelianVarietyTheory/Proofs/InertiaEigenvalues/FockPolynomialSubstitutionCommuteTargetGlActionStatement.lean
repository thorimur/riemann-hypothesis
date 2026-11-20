import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n), fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) = fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  first | exact @GlobalTheory.FockSubstComm.fockSubst_fockT | exact GlobalTheory.FockSubstComm.fockSubst_fockT | (intros; apply GlobalTheory.FockSubstComm.fockSubst_fockT <;> assumption)
