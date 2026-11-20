import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentSmulMemCompletedSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_smul_mem_completedSelfDualLattice : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V := by
  first | exact @GlobalTheory.IdemLat.lamHat_idem | exact GlobalTheory.IdemLat.lamHat_idem | (intros; apply GlobalTheory.IdemLat.lamHat_idem <;> assumption)
