import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.HerrComplexH1

theorem herr_H1_description : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Pr2a D HW F := by
  intro D HW F l _ K s LL h T _
  have H := GlobalTheory.HerrFull.herr_a_and_natural D HW F l K s LL h
  refine ⟨H.2.1 T, fun _ hp => ?_⟩
  have H1 := H.1 (fun e => absurd e hp) T
  exact ⟨H1.1, H1.2.1⟩

end GlobalTheory.NL.HerrComplexH1
