import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
import Development.WeilBound.CoreStatements.PeriodRingComparison.ThetaKernelDeRham.KerThetaEqSpanSymmTBdR
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

def castCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Reformulated.AutPerF.Bcris l (Cmp6.OC l) := RingEquiv.refl _
def castDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Reformulated.AutPerF.BdR l (Cmp6.OC l) := RingEquiv.refl _
def castDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) := RingEquiv.refl _

abbrev equivCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Per6.Bcris l := (castCrystalline l).trans (Cmp6.cBc l)
abbrev equivDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Per6.BdR l := (castDeRham l).trans (Cmp6.cD l)
abbrev equivDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Per6.BdRp l := (castDeRhamPlus l).trans (Cmp6.cP l)

end Formalism.BasicNotions.CmpTie
