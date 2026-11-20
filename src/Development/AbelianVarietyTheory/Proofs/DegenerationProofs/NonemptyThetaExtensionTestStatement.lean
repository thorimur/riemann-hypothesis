import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_thetaExtension_test : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  first | exact @GlobalTheory.ZJ.Core.Theta.nonempty_ext | exact GlobalTheory.ZJ.Core.Theta.nonempty_ext | (intros; apply GlobalTheory.ZJ.Core.Theta.nonempty_ext <;> assumption)
