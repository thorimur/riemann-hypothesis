import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingEulerProductFarRight_of_rapidDecay_unramified : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, GlobalTheory.Core.Rk.IP.EulerRight D := by
  first | exact @GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling | exact GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling | (intros; apply GlobalTheory.Core.Rk.IP.eulerRight_of_unramifiedDoubling <;> assumption)
