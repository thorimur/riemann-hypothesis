import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

theorem exists_split {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (l : Geo.Tor.Level H) :
    ∃ α ∈ l.Mb, ∃ β ∈ Mfr l, α + β = 1 := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by
    rw [Mfr, l.coprime]; exact Submodule.mem_top
  exact Submodule.mem_sup.1 h1

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod
