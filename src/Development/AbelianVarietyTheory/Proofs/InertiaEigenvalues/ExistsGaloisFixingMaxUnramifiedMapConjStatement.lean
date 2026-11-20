import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  first | exact @GlobalTheory.LiftKur.exists_gal_fix_Kur_map | exact GlobalTheory.LiftKur.exists_gal_fix_Kur_map | (intros; apply GlobalTheory.LiftKur.exists_gal_fix_Kur_map <;> assumption)
