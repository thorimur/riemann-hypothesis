import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationComponentUnique
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_component_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ Z, v (e Z) = 0 ∧ ∀ Z', Z' ≠ Z → v (e Z') = ⊤ ∧ ∀ a, ∀ f ∈ cuspOn U h a Z', v f = ⊤) ∧ (∀ la Z, ∃ v ∈ valSet Xo c (algCls Xo c) la, v (e Z) = 0) ∧ ∀ a, (∀ Z, ∀ f ∈ cuspZ Xo c U a, e Z * f ∈ cuspOn U h a Z) ∧ ⨆ Z, cuspOn U h a Z = cuspZ Xo c U a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.valuation_component_unique | exact GlobalTheory.CompanionTheory.Relay.valuation_component_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.valuation_component_unique <;> assumption)
