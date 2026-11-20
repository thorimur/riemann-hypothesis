import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.HostEFK

theorem hypEFK_ev : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), SphericalInertData.HypEFK (w.D Z) :=
  evG_all fun K => lg_all K fun B f T _ _ T' w Z => GlobalTheory.DesignBC.hypEFK (w.D Z)

end GlobalTheory.Mem.HostEFK
