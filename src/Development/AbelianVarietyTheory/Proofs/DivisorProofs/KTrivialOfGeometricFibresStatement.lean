import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTrivialOfGeometricFibres
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_trivial_of_geometric_fibres : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → Out.RelAmple A M → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.KTriv ((Over.pullback y).obj A) (M.pull (pullback.fst A.hom y))) → Out.KTriv A M := by
  first | exact @GlobalTheory.KTrivFibres.kTriv_of_geometricFibres | exact GlobalTheory.KTrivFibres.kTriv_of_geometricFibres | (intros; apply GlobalTheory.KTrivFibres.kTriv_of_geometricFibres <;> assumption)
