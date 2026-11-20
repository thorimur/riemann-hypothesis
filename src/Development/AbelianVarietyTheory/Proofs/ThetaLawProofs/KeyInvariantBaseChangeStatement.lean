import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariant_baseChange : Out.Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (κ : Rˣ), admitted x.P.g n l l' al → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → KaVal x n l l' al s κ → KaVal x' n l l' al s' (Units.map f.toMonoidHom κ) := by
  first | exact @GlobalTheory.KaBaseChange.kaVal_baseChange | exact GlobalTheory.KaBaseChange.kaVal_baseChange | (intros; apply GlobalTheory.KaBaseChange.kaVal_baseChange <;> assumption)
