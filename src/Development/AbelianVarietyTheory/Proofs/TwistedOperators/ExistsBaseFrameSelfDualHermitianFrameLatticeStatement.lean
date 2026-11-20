import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  first | exact @GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | exact GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | (intros; apply GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat <;> assumption)
