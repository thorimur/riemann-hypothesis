import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfProdAddEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.TheRec GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsobaricOfPublished

theorem multiset_eq_of_prod_map_add {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' := by
  first
  | exact @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | (apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq ..)

end GlobalTheory.IsobaricOfPublished

namespace GlobalTheory.IsobaricOfPublished

end GlobalTheory.IsobaricOfPublished
