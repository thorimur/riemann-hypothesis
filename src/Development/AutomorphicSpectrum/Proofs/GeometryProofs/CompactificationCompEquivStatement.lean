import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactification_comp_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ σ, GoodEmb c σ → ∃ κ : Comp Xo c ≃ (U σ).Comp, (∀ Z k, Over (U σ) (e Z) k ↔ k = κ Z) ∧ ∀ Z k, k ≠ κ Z → ∀ y ∈ ((U σ).X k).dom, rdU (U σ) (e Z) k y = 0 ∧ ∀ a, ∀ f ∈ cuspOn U h a Z, rdU (U σ) f k y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.comp_over | exact GlobalTheory.CompanionTheory.Ar.Rec.comp_over | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.comp_over <;> assumption)
