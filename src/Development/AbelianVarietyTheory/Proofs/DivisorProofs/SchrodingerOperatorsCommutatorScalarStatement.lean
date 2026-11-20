import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorsCommutatorScalar
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_operators_commutator_scalar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a b a' b' : κ → mixedEmbedding.mixedSpace F),
    ∃ s : ℂ, ∀ f : SInf F κ, dOp a b (dOp a' b' f) - dOp a' b' (dOp a b f) = s • f := by
  first | exact @GlobalTheory.ThK.EvAt0.PolD.Comm.dOp_comm_scalar | exact GlobalTheory.ThK.EvAt0.PolD.Comm.dOp_comm_scalar | (intros; apply GlobalTheory.ThK.EvAt0.PolD.Comm.dOp_comm_scalar <;> assumption)
