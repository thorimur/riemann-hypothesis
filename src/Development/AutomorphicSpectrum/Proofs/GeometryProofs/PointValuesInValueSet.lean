import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem val_mem_valSet_of_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (y : (Ref.pjSys Xo c).Pt la), (fun f => (Ref.pjSys Xo c).val y f) ∈ valSet Xo c (algCls Xo c) la := by
  intro E _ _ _ H Dw l Xo c la y
  obtain ⟨q, T, io, e, ho, z, hz, t, ht, rfl⟩ := y
  exact ⟨PtV.mk (cls := algCls Xo c) (PY := Unit) (lies := fun _ _ _ _ => True) la ho z hz () trivial, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Rec
