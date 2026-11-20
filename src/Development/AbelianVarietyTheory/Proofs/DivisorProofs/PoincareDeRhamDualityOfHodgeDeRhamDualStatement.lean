import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDual
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareDeRhamDuality_of_hodgeDeRham_dual : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality := by
  first | exact @GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | exact GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge | (intros; apply GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge <;> assumption)
