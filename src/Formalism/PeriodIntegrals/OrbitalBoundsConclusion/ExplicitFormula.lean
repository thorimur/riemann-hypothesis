import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalLemmaOfHelpers

theorem explicitFormula_of : PI.ZerosWindow → PI.DiscFactor → PI.DiscLog → PI.LBoundRight →
    PI.ZetaBoundRight → PI.LInvRight → PI.ExplicitFormula :=
  PI.EF.explicitFormula_main
