import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackConstantBundleDegreeZero
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_constant_bundle_degree_zero : ∀ (K : Type) [Field K] [NumberField K] (M : (Sp (𝓞 K)).Modules) (r : ℕ), GlobalTheory.VB.IsVB M r → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y], IsArithVar p 1 → ∀ q : Y ⟶ Sp (𝓞 K), cxDeg p ((Scheme.Modules.pullback q).obj M) r = 0 := by
  first | exact @GlobalTheory.CxDegIntegers.cxDeg_pullback_eq_zero | exact GlobalTheory.CxDegIntegers.cxDeg_pullback_eq_zero | (intros; apply GlobalTheory.CxDegIntegers.cxDeg_pullback_eq_zero <;> assumption)
