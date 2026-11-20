import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfHyps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_jacquetShalika : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GelfandKazhdanDual :=
  fun hJ hA => gelfandKazhdanDual_of_rapidDecay hJ hA (GlobalTheory.cuspRapidDecaySiegelGL_of_finite hA)

end GlobalTheory.GelfandKazhdanTop
