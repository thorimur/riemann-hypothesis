import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_idealCurveLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  first | exact @GlobalTheory.CurveLattice.exists_periodPair_lamOf | exact GlobalTheory.CurveLattice.exists_periodPair_lamOf | (intros; apply GlobalTheory.CurveLattice.exists_periodPair_lamOf <;> assumption)
