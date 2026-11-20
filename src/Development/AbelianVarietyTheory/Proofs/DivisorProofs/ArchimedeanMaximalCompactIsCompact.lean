import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

namespace GlobalTheory.KinfCompact

theorem compactSpace_Kinf : ∀ I : Formalism.MainNotions.S.AutInst, CompactSpace (GlobalTheory.Dec.Kinf I) := by
  intro I
  letI := I.fF
  letI := I.nF
  haveI : ∀ v : InfinitePlace I.F, CompactSpace (Formalism.REAL.KG (I.ε v)) :=
    fun v => Formalism.REAL.instCompactKG _ _
  exact Pi.compactSpace

end GlobalTheory.KinfCompact
