import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SerreVanishingCubeTotalComplexExactAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serre_vanishing_cubeTotalComplex_exactAt : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ p, (cubeComplex (secCube f (tw M H t) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  first | exact @GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy | exact GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy | (intros; apply GlobalTheory.KeyKa.secCube_tw_exactAt_of_veryAmpleBy <;> assumption)
