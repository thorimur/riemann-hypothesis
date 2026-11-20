import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength

namespace GlobalTheory.Laid

theorem bzfin_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro k _ _ _ _

  exact ⟨CompanionTheory.SmGLBridge.irreducibleAdmissible k, CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    CompanionTheory.BZInd.inductionFiniteLength k, SmGL.IndDual.inductionContragredient k⟩

end GlobalTheory.Laid
