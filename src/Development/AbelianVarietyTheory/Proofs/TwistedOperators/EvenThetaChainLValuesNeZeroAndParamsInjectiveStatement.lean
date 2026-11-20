import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.EvenOnto.chainL_and_inj | exact GlobalTheory.EvenOnto.chainL_and_inj | (intros; apply GlobalTheory.EvenOnto.chainL_and_inj <;> assumption)
