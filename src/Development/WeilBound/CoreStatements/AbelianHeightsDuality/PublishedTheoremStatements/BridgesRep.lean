import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlathFactorisationOfTensorProduct

namespace PositivityTheory.Prw

theorem flathFactorisation_of (h₁ : GlobalTheory.Published.FlathTensorProduct) (h₂ : GlobalTheory.Published.UnitaryIrreducibleAdmissible) :
    GlobalTheory.Published.FlathFactorisation :=
  GlobalTheory.flathFactorisation_of_tensorProduct h₁ h₂

end PositivityTheory.Prw
