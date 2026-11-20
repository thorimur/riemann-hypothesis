import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModel
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_transport_block_model : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_transport | exact GlobalTheory.GaugeQuot.gauge_transport | (intros; apply GlobalTheory.GaugeQuot.gauge_transport <;> assumption)
