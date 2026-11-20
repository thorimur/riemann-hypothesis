import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

private theorem gsp_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) :
    IsGSp (f ν) (g.map f) := by
  have a : adj (g.map f) = (adj g).map f := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  unfold IsGSp at h ⊢
  rw [a, ← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]
