import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_exists : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h → ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | exact GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm | (intros; apply GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm <;> assumption)
