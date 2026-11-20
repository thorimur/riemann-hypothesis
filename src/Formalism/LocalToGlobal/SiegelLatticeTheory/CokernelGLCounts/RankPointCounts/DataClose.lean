import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

noncomputable section

namespace Formalism.L2.SG.DataCut

theorem densInputAt_of_loc {D : Formalism.BasicNotions.D7} (hL : DensLocBound D) : Formalism.L2.SG.DataInst.DensInputAt D :=
  densInputAt_of hL (Formalism.L2.SG.Pf.alpBound_holds D) (Formalism.L2.SG.Pf.placesOver_holds D)

end Formalism.L2.SG.DataCut
