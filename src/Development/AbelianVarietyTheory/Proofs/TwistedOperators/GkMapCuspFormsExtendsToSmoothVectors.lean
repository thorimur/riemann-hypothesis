import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.GKExtensionToSmoothVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gkExtension :
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D :=
  fun h₁ h₂ D => ⟨GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩

end GlobalTheory.GKExtensionToSmoothVectors
