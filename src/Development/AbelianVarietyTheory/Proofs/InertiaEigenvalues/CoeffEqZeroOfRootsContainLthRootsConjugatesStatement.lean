import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfRootsContainLthRootsConjugates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_roots_contain_lth_roots_conjugates : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := by
  first | exact @GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots | exact GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots | (intros; apply GlobalTheory.ExpandCoeff.coeff_eq_zero_of_roots <;> assumption)
