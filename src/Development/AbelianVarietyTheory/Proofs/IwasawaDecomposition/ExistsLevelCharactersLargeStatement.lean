import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelCharactersLarge
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_characters_large : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  first | exact @GlobalTheory.Mem.LevelPrime.exists_levCh_gt | exact GlobalTheory.Mem.LevelPrime.exists_levCh_gt | (intros; apply GlobalTheory.Mem.LevelPrime.exists_levCh_gt <;> assumption)
