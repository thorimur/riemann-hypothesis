import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPolarisedAbelianSchemeBaseChangeRingAction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_baseChange_ringAction : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (P₀ : Out.PolAV (Geo.Tor.Sp T)), ∃ (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ ∧ Geo.Tor.LBIso P.L (P₀.L.pull φ) ∧ P.g = P₀.g ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] (o₀ : P₀.OAct OE), ∃ o : P.OAct OE, ∀ a, (o.act a).left ≫ φ = φ ≫ (o₀.act a).left := by
  first | exact @GlobalTheory.exists_polBaseChange_oAct | exact GlobalTheory.exists_polBaseChange_oAct | (intros; apply GlobalTheory.exists_polBaseChange_oAct <;> assumption)
