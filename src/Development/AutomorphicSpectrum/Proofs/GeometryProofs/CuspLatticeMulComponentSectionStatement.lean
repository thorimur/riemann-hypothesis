import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspLatticeMulComponentSection
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_lattice_mul_component_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (a : WZ E) (Z : Comp Xo c) (w : Rul Xo c), w ∈ (Ref.pjSys Xo c).lat (cuspZ Xo c U a) → e Z * w ∈ latOn U h a Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn | exact GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.indicator_mul_mem_latOn <;> assumption)
