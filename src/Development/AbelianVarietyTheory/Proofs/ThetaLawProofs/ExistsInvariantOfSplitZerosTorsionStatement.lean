import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsInvariantOfSplitZerosTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_of_split_zeros_torsion : Out.Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) (ξ : Fin (degProd x.P.g n l l' ^ (2 * x.P.g)) → Pt x), admitted x.P.g n l l' al → IsUnit ((degProd x.P.g n l l' : ℕ) : R) → EtZ x s z ch → (∀ a, ξ a ^ degProd x.P.g n l l' = 1) → (∀ a a', a ≠ a' → ∀ p : Sp R, (ξ a).left p ≠ (ξ a').left p) → ∃ κ, KaVal x n l l' al s κ := by
  first | exact @GlobalTheory.exists_kaVal_of_split | exact GlobalTheory.exists_kaVal_of_split | (intros; apply GlobalTheory.exists_kaVal_of_split <;> assumption)
