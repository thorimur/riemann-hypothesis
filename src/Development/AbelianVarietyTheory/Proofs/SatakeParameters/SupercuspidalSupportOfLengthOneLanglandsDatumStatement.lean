import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportOfLengthOneLanglandsDatum

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_of_lengthOne_langlandsDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : ℕ) (Δ : Fin c → Segment k) (x : IrrGL k), (∀ i, (Δ i).len = 1) →
    IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep →
    HasSupport x.rep (Finset.univ.val.map fun i => (Δ i).first) := by
  first | (exact @GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one) | (exact GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one) | (intros; apply GlobalTheory.LocGL.LenOneSupport.hasSupport_first_of_isL_len_one  <;> assumption)
