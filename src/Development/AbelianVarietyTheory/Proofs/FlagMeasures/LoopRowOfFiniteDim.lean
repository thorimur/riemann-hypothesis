import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowsOfLargeGapDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBesselStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RanksFramesClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn

namespace GlobalTheory.LoopRowsByName

theorem loopRows_of_rowsFinDim :
    Formalism.L2.SG.RowsDef.RowsFinDim → (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 →
      ∀ sel : SSel 𝒞, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → LoopRowS 3 𝒞 sel := by
  intro hFin hUT 𝒞 hT sel hTu
  exact GlobalTheory.T.loopRows_of_large_gap_discreteSeries (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2 GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional
    GlobalTheory.wuDecayOfGap hFin 𝒞 sel hTu (GlobalTheory.ranks_and_frame_of_tied_class hUT 𝒞 hT).1

end GlobalTheory.LoopRowsByName
