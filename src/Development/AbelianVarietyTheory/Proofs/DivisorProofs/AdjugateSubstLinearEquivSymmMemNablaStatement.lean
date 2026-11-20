import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNabla

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  first | exact @GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | exact GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | (intros; apply GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr <;> assumption)
