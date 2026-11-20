import Development.EtaleCohomology.EtaleSheaves.MVSpcPf
import Development.EtaleCohomology.TateTwists.EtaleMayerVietorisShortExactSequenceFreeOfCompon

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafMVVanishPf

theorem mvSpc : LateralTheory.E.MVPf.MVSpc :=
  LateralTheory.E.MVPf.MVSpc_of (fun R _ _ _ _ f g h => LateralTheory.Fin.EtaleMayerVietorisChainsShortExact.intersectionNumber_baseChange R f g h)

end LateralTheory.E.LeafMVVanishPf

namespace LateralTheory.E.E8
open LateralTheory.E.LeafMVVanishPf

end LateralTheory.E.E8
