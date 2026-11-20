import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFreeRankDegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_free_rank_degree : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (R : Type) [CommRing R] [IsLocalRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Free R X.Lie ∧ Module.Finite R X.Lie ∧ Module.finrank R X.Lie = Module.finrank ℚ F := by
  first | exact @GlobalTheory.Lie.free_finrank_of_isLocalRing | exact GlobalTheory.Lie.free_finrank_of_isLocalRing | (intros; apply GlobalTheory.Lie.free_finrank_of_isLocalRing <;> assumption)
