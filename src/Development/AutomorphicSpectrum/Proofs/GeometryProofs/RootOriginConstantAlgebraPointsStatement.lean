import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginConstantAlgebraPoints
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_constant_algebra_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), letI := Small.cstAlg Or; ∀ (y₂ y' : FrPt Xo c RM.Ω), Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f → y'.x = y₂.x → ∀ (s : CMType H ⊕ CMType H) (w : Fin (labelRk Dw s) → Or.𝔐.Li), (∀ k, (Or.𝔐.M.pt (w k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k)) → ∀ (cf : Fin (Dw.mult (Small.labelC s)) → RM.Ω) (k : Fin (labelRk Dw s)), IsCombAt y₂.x (y₂.u (Small.labelC s)) cf (y'.u (Small.labelC s) (Small.labelFin Dw s k)) → (Or.𝔐.M.pt (∑ m, cf (Small.labelFin Dw s m) • w m)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points | exact GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points <;> assumption)
