import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompositionGroupEquivPadicGalois
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompositionGroup_equiv_padicGalois : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  first | exact @GlobalTheory.DecGalois.exists_continuousMulEquiv | exact GlobalTheory.DecGalois.exists_continuousMulEquiv | (intros; apply GlobalTheory.DecGalois.exists_continuousMulEquiv <;> assumption)
