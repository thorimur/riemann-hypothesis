import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Rigid

theorem strings_eq_map {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) :
    strings p d = ∑ x : (Σ i, Fin (d i)), ({(p x.1, spehExp (d x.1) x.2)} : Multiset (X × ℝ)) := by
  unfold strings
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_multiset_sum]
  exact (Multiset.sum_map_singleton _).symm.trans (by rw [Multiset.map_map]; rfl)

theorem strings_eq_of_equiv {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ)
    (s : (Σ i, Fin (d i)) ≃ (Σ j, Fin (d' j)))
    (hs : ∀ x, p x.1 = p' (s x).1 ∧ spehExp (d x.1) x.2 = spehExp (d' (s x).1) (s x).2) :
    strings p d = strings p' d' := by
  rw [strings_eq_map, strings_eq_map]
  refine Fintype.sum_equiv s _ _ fun x => ?_
  rw [(hs x).1, (hs x).2]

end GlobalTheory.Rigid
