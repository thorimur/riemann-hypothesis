import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmptyPiTensorIsSubquotientJacquetModuleDegreeZer
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.emptyPiTensor_isSubquotient_jacquetModule_degreeZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  first | exact @GlobalTheory.piTensor_isSubquotient_jac_degZero | exact GlobalTheory.piTensor_isSubquotient_jac_degZero | (intros; apply GlobalTheory.piTensor_isSubquotient_jac_degZero <;> assumption)
