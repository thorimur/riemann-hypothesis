import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleSingleBlockSelf
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := by
  first | exact @GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | exact GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | (intros; apply GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac <;> assumption)
