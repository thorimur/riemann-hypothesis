import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ], {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧ ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  first | exact @GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | exact GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one | (intros; apply GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one <;> assumption)
