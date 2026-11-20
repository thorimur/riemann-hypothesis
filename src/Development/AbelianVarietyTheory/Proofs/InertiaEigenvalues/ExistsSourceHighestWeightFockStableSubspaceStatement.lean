import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSourceHighestWeightFockStableSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sourceHighestWeight_fock_stable_subspace : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  first | exact @GlobalTheory.exists_nHw_of_fockS_stable | exact GlobalTheory.exists_nHw_of_fockS_stable | (intros; apply GlobalTheory.exists_nHw_of_fockS_stable <;> assumption)
