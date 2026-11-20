import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMinorsUnipotentMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minors_unipotent_mul : ∀ (R : Type) [CommRing R] (m : ℕ) (n : Low m → R) (M : Matrix (Fin m) (Fin m) R), M.BlockTriangular id → ∀ l : Fin (m + 1), ((uniR n * M).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det = (M.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
  first | exact @GlobalTheory.FlagCell.det_leading_uniR_mul | exact GlobalTheory.FlagCell.det_leading_uniR_mul | (intros; apply GlobalTheory.FlagCell.det_leading_uniR_mul <;> assumption)
