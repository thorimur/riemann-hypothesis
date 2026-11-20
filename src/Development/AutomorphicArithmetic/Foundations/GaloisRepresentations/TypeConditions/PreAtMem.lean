import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts

noncomputable section

namespace UpperTheory.GalS

structure Core0 (D : D7) : Prop where
  what₂ : GlobalTheory.NRows.Rows D
  adm : SumRepresentations.admitted D
  Conclusion1 : SumRepresentations.Conclusion1 D
  z : SumRepresentations.ConclusionZ D
  rhoBar : ResidualIrreducibleRankR D
  g3p : AdmissibleThreePrime.LabelDegreeHypotheses D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D

end UpperTheory.GalS
