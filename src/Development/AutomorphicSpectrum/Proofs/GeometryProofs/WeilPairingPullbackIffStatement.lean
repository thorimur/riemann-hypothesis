import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (k : Type) [Field k] (z : Sp k ⟶ S') (a' b' : Over.mk z ⟶ t'.G) (a b : Over.mk (z ≫ f) ⟶ t.G) (n : ℕ) (c : kˣ), a'.left ≫ m.φ = a.left → b'.left ≫ m.φ = b.left → (Out.WeilIs t'.G t'.PP.L n a' b' (unitOn c) ↔ Out.WeilIs t.G t.PP.L n a b (unitOn c)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WeilPull.main | exact GlobalTheory.CompanionTheory.Ar.WeilPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.WeilPull.main <;> assumption)
