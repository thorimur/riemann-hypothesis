import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HermFrameHolds

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.H (localStandard kappaExists)

theorem frameExistsH : FrameExistsH := FrP.hermFrame_holds

theorem uniformGaussModels_fact_variant : ThetaFourthPowerShapeNormalised := theta_kappa_shape_holds localStandard kappaExists

theorem frobExistsH : FrobExistsH := by
  intro l _ hl
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l (by omega)
  exact ⟨σ, hσ⟩

end Formalism.L2.Th1.Top
