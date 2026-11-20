import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPoints
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_map_at_fitted_points : GlobalTheory.BigTop.Fun.Bundle → GlobalTheory.BigTop.Fun.SetAt → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → GlobalTheory.BigTop.Fun.OneMap @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.oneMap_of_rows | exact GlobalTheory.BigTop.Fun.oneMap_of_rows | (intros; apply GlobalTheory.BigTop.Fun.oneMap_of_rows <;> assumption)
