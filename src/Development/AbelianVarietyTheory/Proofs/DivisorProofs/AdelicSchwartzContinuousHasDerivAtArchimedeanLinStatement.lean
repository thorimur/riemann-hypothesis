import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧ ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ), HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  first | exact @GlobalTheory.ArchDecay.SchLine.schline | exact GlobalTheory.ArchDecay.SchLine.schline | (intros; apply GlobalTheory.ArchDecay.SchLine.schline <;> assumption)
