import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientOfExactMiddleIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_of_exact_middle_irreducible : ∀ (G : Type) [Group G] (U V A Q : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup Q] [Module ℂ Q] (τ : Representation ℂ G U) (ρ : Representation ℂ G V) (α : Representation ℂ G A) (κ : Representation ℂ G Q) (i : α.IntertwiningMap ρ) (q : ρ.IntertwiningMap κ), τ.IsIrreducible → (∀ v, q v = 0 → ∃ a, i a = v) → IsSubquotient τ ρ → IsSubquotient τ α ∨ IsSubquotient τ κ := by
  first | exact @GlobalTheory.isSubquotient_of_exact_middle | exact GlobalTheory.isSubquotient_of_exact_middle | (intros; apply GlobalTheory.isSubquotient_of_exact_middle <;> assumption)
