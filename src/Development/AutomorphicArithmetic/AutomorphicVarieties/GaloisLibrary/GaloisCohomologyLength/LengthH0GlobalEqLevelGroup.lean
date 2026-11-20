import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelGroupSupLevelInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {N : ℕ} [NeZero N] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K)

section

variable {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}

include φ

theorem princ_le_ineImage (hv : v ∈ Above F l) (hA : IsPlaceOver A v) :
    KStar.TotallyRealRoots.princ l (N.factorization l) ≤ ineImage F l A :=
  (KStar.TotallyRealRoots.princ_le_levelGroup N _).1.trans (levelLeIne F Ω N K φ l v A hv hA)

end

include φ

end

end UpperTheory.V.LDataCardLeFinrank

end
