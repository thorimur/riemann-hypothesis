import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem gram_xi_eq_of_lawsFull {D : D7} {T : Full D} (h : LawsFull T) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  intro j hj k k'

  obtain ⟨hr, hW⟩ := h.j.modelW j hj T.J.σ₀ T.J.good_σ₀
  obtain ⟨hG, hξ⟩ := hW k
  obtain ⟨hG', hξ'⟩ := hW k'
  exact ⟨hG.trans hG'.symm, hξ.trans hξ'.symm⟩

end GlobalTheory.Dict
