import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOfIsRootMinpolyUnramifiedRootsOfUnityField
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eq_of_isRoot_minpoly_unramifiedRootsOfUnityField : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := by
  first | exact @GlobalTheory.conj_norm_eq_of_minpoly_root | exact GlobalTheory.conj_norm_eq_of_minpoly_root | (intros; apply GlobalTheory.conj_norm_eq_of_minpoly_root <;> assumption)
