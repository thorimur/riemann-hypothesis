import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.PerSLat

namespace PI.Dv.Tr

theorem degPart : DegPart := degPart_of splitBound perSBound

theorem dvTransfer_main : PI.Dv.Conclusion4a := trace_formula_of_rank_degree rankPart degPart muPart

end PI.Dv.Tr
