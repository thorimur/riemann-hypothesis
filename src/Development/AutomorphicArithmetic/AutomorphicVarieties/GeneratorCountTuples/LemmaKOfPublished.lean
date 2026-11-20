import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Reduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.TorsMain

open Formalism.GaloisCohomology

namespace UpperTheory.V.K

theorem lemmaK (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) (hK : KBridge) :
    ∃ CK : ℝ, 0 < CK ∧ LemmaK CK :=
  lemmaK_of hP hF hT hK UpperTheory.V.KT.torsMain

end UpperTheory.V.K
