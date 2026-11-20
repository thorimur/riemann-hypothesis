import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjection
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartComponents_finite_projection : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite <;> assumption)
