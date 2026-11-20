import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJets

noncomputable section

namespace GlobalTheory.LiftTypePrime.ProdComb

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.KernelAt GlobalTheory.ProductJets GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

variable {D : D7} {N N' : ℕ}

theorem mem_stdL {x : Fin N → D.host.E} : x ∈ stdL D N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x k, h⟩, rfl⟩⟩

theorem eqAt_std {p : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (h : StdAt D p L) : EqAt D p L (stdL D N) := by
  obtain ⟨L₀, h0, h⟩ := h
  rwa [show stdL D N = L₀ from Submodule.ext fun x => mem_stdL.trans (h0 x).symm]

end GlobalTheory.LiftTypePrime.ProdComb

end
