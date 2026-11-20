import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_twist_bound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  first | exact @GlobalTheory.CompanionTheory.TotalTrace.twBound | exact GlobalTheory.CompanionTheory.TotalTrace.twBound | (intros; apply GlobalTheory.CompanionTheory.TotalTrace.twBound <;> assumption)
