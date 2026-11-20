import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofinite

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ Formalism.MainNotions.StandardLatticesGL3.InertQ D p) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.NormSum.VacInt.part D (fun p => p ∉ s) y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertCofinite.intG_part_cofinite | exact GlobalTheory.InertCofinite.intG_part_cofinite | (intros; apply GlobalTheory.InertCofinite.intG_part_cofinite <;> assumption)
