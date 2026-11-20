import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateWeightNonnegRadius
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSubst_coordinate_weight_nonneg_radius : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ (c : I) (μ : Fin N →₀ ℕ), V.Ge (-((μ.degree : ℝ) / ((V.l : ℝ) - 1))) (MvPowerSeries.coeff μ (linPull e (t c))) := by
  first | exact @GlobalTheory.MainTerm.linPull_coord_weight_nonneg | exact GlobalTheory.MainTerm.linPull_coord_weight_nonneg | (intros; apply GlobalTheory.MainTerm.linPull_coord_weight_nonneg <;> assumption)
