import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.InfFamUnique

theorem existsUnique_infFam : ∀ D : D7, ∃! θ : InfF D, IsInfFam θ := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  exact ⟨θ, hθ, fun θ' h' => funext fun ρ =>
    GlobalTheory.Mem.VolEmb.infEmb_unique (tauE D ρ) (θ' ρ) (θ ρ) (h' ρ) (hθ ρ)⟩

end GlobalTheory.Mem.InfFamUnique
