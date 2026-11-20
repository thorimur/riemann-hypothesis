import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalityOfThetaHypotheses
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationality_of_theta_hypotheses : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  first | exact @GlobalTheory.RowTestAssembly.rowTest_atDat_of_join | exact GlobalTheory.RowTestAssembly.rowTest_atDat_of_join | (intros; apply GlobalTheory.RowTestAssembly.rowTest_atDat_of_join <;> assumption)
