import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.IntegralDenom

theorem exists_denom_not_mem : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  intro E _ _ w a ha
  exact GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem w a ha

end GlobalTheory.IntegralDenom
