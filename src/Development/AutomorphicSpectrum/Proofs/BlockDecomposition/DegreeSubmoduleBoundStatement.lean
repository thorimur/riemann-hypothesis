import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBound
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
