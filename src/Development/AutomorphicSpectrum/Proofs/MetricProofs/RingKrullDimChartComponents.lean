import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

theorem chartComponents_dim : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  intro K _ _ ι _ Q e m σ i hQ J hJ
  have hmin : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes :=
    mem_chartComponents.mp hJ
  have hhom : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  exact segChart_dim hQ.2.1.1 hhom hQ.2.2 σ i hmin

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
