import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamMemLpOfNe

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem isDS_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ v₀) := by
  unfold Formalism.MainNotions.S.IsDS
  refine ⟨?_, Hlam_nontrivial hgap hP hv₀, sigLam_isURepOn hgap hP hv₀, sigLam_irred hgap hP hv₀,
    sqInt_sigLam hgap hP hv₀, ⟨_, (sigLam_lowK hgap hP hv₀).1⟩,
    fun μ S hS => (sigLam_kType_bounds hgap hP hv₀ S hS).1⟩
  first
    | infer_instance
    | (unfold Hlam closGen
       exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe)

end ReciprocityTheory.ChartRestriction.DS.G2
