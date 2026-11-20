import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopNadel
import Development.WeilBound.CoreStatements.AutomorphicKernels.NadelVanishing.TopIsolated

namespace NadelVanishingSeparation.NSI

theorem nadelVanishingAndNonKltDivisor : GlobalTheory.Published.NadelVanishingAndNonKltDivisor :=
  ⟨nadelVanishingPair, isolatedNonKltDivisor⟩

end NadelVanishingSeparation.NSI
