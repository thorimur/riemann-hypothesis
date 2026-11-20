import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂

theorem aux_of_blochKato_tateDuality_eulerChar₂ :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ D : D7, LocalSituation.Conclusion5 D :=
  GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato

end GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂
