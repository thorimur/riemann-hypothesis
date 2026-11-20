import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PackOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSmooth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfEx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ActHcsSlice
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PFinInvMulInfGL

open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

theorem smoothOf_holds : SmoothOf := smoothOf tensTest

theorem actVal_of (h : MultAlg) : ActVal := actVal h compatFub tensTest

theorem pack_of_gel (hS : SizeBasic) (hB : Bridge.BridgeSt) (hG : GelOf) : Pack :=
  pack_of tensTest typeOf smoothOf_holds (growthOf hS) hG infEx (PAut.autOf hB)

end PositivityTheory.Rg.BcB.CG
