import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec

namespace SharpLaws

theorem card_psi (D : D7) (Q : Par D) : Fintype.card (CMType Q.H) = D.R.f := by
  have h := GlobalTheory.PeriodCoord.card_cmType Q.H
  rw [Nat.card_eq_fintype_card, D.host.finrank_cmField] at h
  rw [h]
  show 4 * D.R.ord / 2 = 2 * D.R.ord
  omega

end SharpLaws

end GlobalTheory.CompanionTheory.Ar.Rec
