import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIsCompact
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_maximal_compact_is_compact : ∀ I : Formalism.MainNotions.S.AutInst, CompactSpace (GlobalTheory.Dec.Kinf I) := by
  first | exact @GlobalTheory.KinfCompact.compactSpace_Kinf | exact GlobalTheory.KinfCompact.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompact.compactSpace_Kinf <;> assumption)
