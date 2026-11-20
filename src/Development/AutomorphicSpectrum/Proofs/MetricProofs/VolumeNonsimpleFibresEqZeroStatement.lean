import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeNonsimpleFibresEqZero
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_nonsimple_fibres_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | exact GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxOnly.cxSimple_only_null <;> assumption)
