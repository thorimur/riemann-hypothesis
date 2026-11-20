import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2

theorem UpperTheory.V.Lit.infEx :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lit.InfEx :=
  fun _ _ _ _ _ _ π v => UpperTheory.V.TR.Cen.exists_hasInfChar π v
