import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBesselPeriodSesquilinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBesselPeriod_sesquilinear : ∀ D : D7, PosLin D := by
  first | exact @GlobalTheory.RootExch.PosLinear.posLin | exact GlobalTheory.RootExch.PosLinear.posLin | (intros; apply GlobalTheory.RootExch.PosLinear.posLin <;> assumption)
