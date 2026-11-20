import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv

open UpperTheory.Top UpperTheory.V.HV UpperTheory.V.HV.U

namespace UpperTheory.V.Th

theorem cohInp (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hK : K.KBridge) : U3.CohInp where
  loc := localGaloisCohomology₂ hN
  pt := hN.coh.pt
  gf := hN.coh.gf
  ge := hN.coh.ge
  lemK := lemmaK hN hK

theorem caseI (h : InpU) (ha : Aut.AutomorphyUnramifiedCoefficients) : CountI := U3.countI (U3.corGK (U3.propGK h.number (oneChar h ha)))

end UpperTheory.V.Th
