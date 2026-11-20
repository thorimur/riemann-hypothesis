import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | exact GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul | (intros; apply GlobalTheory.NormaliserGLint.conj_eq_glint_mul_mul <;> assumption)
