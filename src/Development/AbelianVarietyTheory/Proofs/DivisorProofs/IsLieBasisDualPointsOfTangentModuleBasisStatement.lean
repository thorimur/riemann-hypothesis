import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  first | exact @GlobalTheory.VertCoeffRing.isLieBasis_tvE | exact GlobalTheory.VertCoeffRing.isLieBasis_tvE | (intros; apply GlobalTheory.VertCoeffRing.isLieBasis_tvE <;> assumption)
