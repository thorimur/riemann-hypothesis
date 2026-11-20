import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_goodSplitPlaces : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  first | exact @GlobalTheory.FrobDense.frob_dense_goodSplit | exact GlobalTheory.FrobDense.frob_dense_goodSplit | (intros; apply GlobalTheory.FrobDense.frob_dense_goodSplit <;> assumption)
