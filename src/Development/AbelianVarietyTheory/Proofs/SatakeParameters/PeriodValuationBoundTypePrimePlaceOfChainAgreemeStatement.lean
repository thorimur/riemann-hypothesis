import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup), TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  first | exact @GlobalTheory.ColPeriodTies.boundAt_of_ties | exact GlobalTheory.ColPeriodTies.boundAt_of_ties | (intros; apply GlobalTheory.ColPeriodTies.boundAt_of_ties <;> assumption)
