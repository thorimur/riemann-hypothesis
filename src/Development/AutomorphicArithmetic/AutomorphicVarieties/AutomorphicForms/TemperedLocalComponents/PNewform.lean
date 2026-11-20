import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep
open NumberField GlobalTheory.CuspRep UpperTheory.V

theorem UpperTheory.V.Af.newformRep :
    UpperTheory.V.Published.NewformRep :=
  UpperTheory.V.Af.newformRepOf UpperTheory.V.Af.cuspSemisimpleReal UpperTheory.V.Af.admissibleReal
