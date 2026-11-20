import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.VwinOfInputs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalU

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.Core

open UpperTheory.V.Lit UpperTheory.V.W

theorem countI (hN : LitN) (hK : ∃ CK : ℝ, LemmaK CK) (hKa : KatoUseN) (adK : Af.AdVanishK) (adQ : Af.AdVanishQ)
    (nw : Af.NewformAut) (nU : Af.CongruenceNumberRankThree) (h3 : Aut.AutomorphyUnramifiedCoefficients) : CountI :=
  KN.O.caseI
    { loc := U.localGaloisCohomology₂ hN, pt := hN.coh.pt, gf := hN.coh.gf, ge := hN.coh.ge, lemK := hK, lemM := Alg.M.main_holds,
      lemM' := Alg.M.mprime_holds, lemP := Alg.lemmaP, kato := hKa, adK := adK, adQ := adQ, newAut := nw, number := nU } h3

end UpperTheory.V.HV.Core
