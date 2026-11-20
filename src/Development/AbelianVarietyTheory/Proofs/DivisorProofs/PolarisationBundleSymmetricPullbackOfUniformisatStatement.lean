import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleSymmetricPullbackOfUniformisat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationBundle_symmetric_pullback_of_uniformisation : AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, LBIso U.LG.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → GlobalTheory.PolDeg.IsPrim D.toPre.P (o.onB.act w) := by
  first | exact @GlobalTheory.PrimDescent.isPrim_of_unif | exact GlobalTheory.PrimDescent.isPrim_of_unif | (intros; apply GlobalTheory.PrimDescent.isPrim_of_unif <;> assumption)
