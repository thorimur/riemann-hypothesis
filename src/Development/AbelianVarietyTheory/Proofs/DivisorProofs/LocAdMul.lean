import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

noncomputable section

namespace GlobalTheory.UnipEmb

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

def locAd (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F) ∘ₗ singleFin v

theorem locAd_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) : locAd F v (a * b) = locAd F v a * locAd F v b :=
  Prod.ext (mul_zero _).symm (singleFin_mul v a b)

def locInc (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₙ+* AF F ⊗[F] E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (locAd F v) (locAd_mul F v)

end GlobalTheory.UnipEmb

end
