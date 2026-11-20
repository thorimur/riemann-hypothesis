import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm
theorem resNe : ∀ (K : Type) [Field K] (P Q : K[X]), P.Monic → Q.Monic → IsCoprime P Q → resultant P Q ≠ 0 := by
  intro K _ P Q _ _ hc
  exact Polynomial.resultant_ne_zero P Q hc

theorem resMap : ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (P Q : K[X]),
    resultant (P.map f) (Q.map f) = f (resultant P Q) := by
  intro K L _ _ f P Q
  rw [Polynomial.natDegree_map, Polynomial.natDegree_map]
  exact Polynomial.resultant_map_map P Q _ _ f
end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

end GlobalTheory.ProdForm
