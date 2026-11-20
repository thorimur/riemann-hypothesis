import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.OneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv

open UpperTheory.Top UpperTheory.V.HV UpperTheory.V.HV.U

namespace UpperTheory.V.Z.Kato

theorem corGK_of (h : InpZ) (ha : Aut.AutomorphyUnramifiedCoefficients) : U3.CorGK := U3.corGK (U3.propGK h.number (oneChar h ha))

theorem caseI (h : InpZ) (ha : Aut.AutomorphyUnramifiedCoefficients) : CountI := U3.countI (corGK_of h ha)

end UpperTheory.V.Z.Kato
