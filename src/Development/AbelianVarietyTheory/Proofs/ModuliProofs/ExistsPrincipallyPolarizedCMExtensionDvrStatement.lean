import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp V)) [GrpObj A] (tK : SAB H (Sp K)) (φ : tK.G.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback tK.G A (spMap (algebraMap V K)) φ → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → ∃ (t : SAB H (Sp V)) (ν : SABMap tK t (spMap (algebraMap V K))) (e : t.G ≅ A), ν.φ ≫ e.hom.left = φ ∧ IsMonHom e.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.GoodPol.exists_sab_of_generic | exact GlobalTheory.GoodPol.exists_sab_of_generic | (intros; apply GlobalTheory.GoodPol.exists_sab_of_generic <;> assumption)
