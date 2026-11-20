import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentre
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧ ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  first | exact @GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | exact GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | (intros; apply GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete <;> assumption)
