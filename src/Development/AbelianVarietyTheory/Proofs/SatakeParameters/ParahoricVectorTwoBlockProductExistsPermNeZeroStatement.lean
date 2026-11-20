import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZero
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  first | exact @GlobalTheory.ParahoricPerm.exists_perm_ne_zero | exact GlobalTheory.ParahoricPerm.exists_perm_ne_zero | (intros; apply GlobalTheory.ParahoricPerm.exists_perm_ne_zero <;> assumption)
