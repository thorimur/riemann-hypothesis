import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

namespace Formalism.FourierDecayAlt.P.Wd13

open Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P.Wd13

namespace Formalism.FourierDecayAlt.P

theorem word_statements_all_hold : Formalism.FourierDecayAlt.Wd.WordsAll :=
  ⟨word_module_structure, site_exchange_relation, word_matrix_entry_one, conjugate_word_eigen, word_product_formula,
    duality_list_holds, kappa_formula_holds, plane_wave_vector_identity, plane_wave_word_identity⟩

end Formalism.FourierDecayAlt.P
