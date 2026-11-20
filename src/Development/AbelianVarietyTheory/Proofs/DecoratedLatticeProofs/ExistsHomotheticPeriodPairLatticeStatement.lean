import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homothetic_periodPair_lattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair, (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧ (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧ L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  first | exact @GlobalTheory.homotheticLattice | exact GlobalTheory.homotheticLattice | (intros; apply GlobalTheory.homotheticLattice <;> assumption)
