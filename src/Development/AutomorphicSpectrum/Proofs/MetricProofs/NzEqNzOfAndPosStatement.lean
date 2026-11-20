import Development.AutomorphicSpectrum.Proofs.MetricProofs.NzEqNzOfAndPos
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nz_eq_nzOf_and_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | exact GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.NzCase.nz_eq_nzOf_of_family <;> assumption)
