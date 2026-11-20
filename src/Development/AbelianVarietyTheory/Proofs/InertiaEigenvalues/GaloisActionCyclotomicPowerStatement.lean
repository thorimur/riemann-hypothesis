import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_cyclotomic_power : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  first | exact @GlobalTheory.BKReal.gal_wA_pow | exact GlobalTheory.BKReal.gal_wA_pow | (intros; apply GlobalTheory.BKReal.gal_wA_pow <;> assumption)
