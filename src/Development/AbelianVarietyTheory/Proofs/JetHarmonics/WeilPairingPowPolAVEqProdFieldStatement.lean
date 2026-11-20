import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_powPolAV_eq_prod_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  first | exact @GlobalTheory.WeilPower.weilIs_pow_field | exact GlobalTheory.WeilPower.weilIs_pow_field | (intros; apply GlobalTheory.WeilPower.weilIs_pow_field <;> assumption)
