import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedVanishingOnCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_vanishing_on_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (a : cIndSpace (HPG k i t) (hRep τ σ)), (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.eq_zero_of_fibV_eq_zero <;> assumption)
