import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientEigenvector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_subquotient_eigenvector : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧ ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  first | exact @GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | exact GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero | (intros; apply GlobalTheory.VecSubquot.exists_irreducible_subquotient_of_ne_zero <;> assumption)
