import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet

namespace Formalism.LatticeIndexTer

theorem latFinite : LatFinite := lattice_quotient_finite
theorem latBasis : LatBasis := lattice_has_basis
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
