import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily

namespace GlobalTheory.Fc.S0

structure Hypotheses2 : Prop extends Hypotheses1 where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport

end GlobalTheory.Fc.S0
