import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadrat
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) := by
  first | exact @GlobalTheory.Mem.HostEFK.hypEFK_ev | exact GlobalTheory.Mem.HostEFK.hypEFK_ev | (intros; apply GlobalTheory.Mem.HostEFK.hypEFK_ev <;> assumption)
