import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem zIdem_eq_charIdem {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) :
    zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem zIdem_centralIdempotent : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ →
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := by
  intro Γ _ _ τ hτ
  have h := orthogonalCentral Γ τ τ hτ hτ
  rw [zIdem_eq_charIdem]
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end GlobalTheory.SerOSys
