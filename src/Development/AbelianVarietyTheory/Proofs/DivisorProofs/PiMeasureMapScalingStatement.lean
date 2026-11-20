import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMeasureMapScaling

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_measure_map_scaling : ∀ {α : Type} [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν] (f : α → α), Measurable f → ∀ c : ENNReal, c ≠ ⊤ →
  ν.map f = c • ν → ∀ k : ℕ, (Measure.pi fun _ : Fin k => ν).map (fun v i => f (v i)) = c ^ k • Measure.pi fun _ : Fin k => ν := by
  first | exact @GlobalTheory.CoordPowScale.map_pi_coord_eq_pow_smul | exact GlobalTheory.CoordPowScale.map_pi_coord_eq_pow_smul | (intros; apply GlobalTheory.CoordPowScale.map_pi_coord_eq_pow_smul <;> assumption)
