import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatRowTest
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
open GlobalTheory.RowClaim

namespace GlobalTheory.Twist

theorem atDat_rowTest_of_exField : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → GlobalTheory.RowEx.ExField → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun hG hC h1 h2 h3 h4 h5 h6 h7 hE => GlobalTheory.Mem.R3.Rw.RowAt.atDat_rowTest hG hC h1 h2 h3 h4 h5 h6 h7 hE

end GlobalTheory.Twist
