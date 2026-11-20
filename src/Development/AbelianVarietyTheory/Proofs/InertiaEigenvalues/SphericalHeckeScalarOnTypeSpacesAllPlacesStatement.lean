import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ i : D.nd.Loc, HeckeScalar M i := by
  first | exact @GlobalTheory.HeckeScalarAll.heckeScalar_all | exact GlobalTheory.HeckeScalarAll.heckeScalar_all | (intros; apply GlobalTheory.HeckeScalarAll.heckeScalar_all <;> assumption)
