import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W), Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  first | exact @GlobalTheory.IdemRankLocal.rank_map_const | exact GlobalTheory.IdemRankLocal.rank_map_const | (intros; apply GlobalTheory.IdemRankLocal.rank_map_const <;> assumption)
