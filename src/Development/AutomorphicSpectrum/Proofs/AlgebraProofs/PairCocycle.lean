import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement

namespace GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem pairCocycle : PairCocycle.Statement :=
  PairCocycle.proof GlobalTheory.T.flag_independence GlobalTheory.T.vertical_divisors_commute IntNumAddFirst.full

end GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed
