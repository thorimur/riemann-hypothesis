import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  first | exact @GlobalTheory.HTObjExt.extends_obj | exact GlobalTheory.HTObjExt.extends_obj | (intros; apply GlobalTheory.HTObjExt.extends_obj <;> assumption)
