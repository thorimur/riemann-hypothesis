import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.OneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv

open UpperTheory.Top UpperTheory.V.HV UpperTheory.V.HV.U

namespace UpperTheory.V.Lit.KN.O

theorem corGK_of (h : InpN) (ha : Aut.AutomorphyUnramifiedCoefficients) : U3.CorGK := U3.corGK (U3.propGK h.number (oneChar h ha))

theorem caseI (h : InpN) (ha : Aut.AutomorphyUnramifiedCoefficients) : CountI := U3.countI (corGK_of h ha)

end UpperTheory.V.Lit.KN.O
