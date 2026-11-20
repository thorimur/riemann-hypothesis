import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOne
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | exact GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix <;> assumption)
