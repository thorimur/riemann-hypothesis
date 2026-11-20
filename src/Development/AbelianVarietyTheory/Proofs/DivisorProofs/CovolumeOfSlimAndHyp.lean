import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeOfHeightPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Ch2ConstantExistsStatement
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem covolX_of_slim₂ (hS : Slim) (hX : GlobalTheory.CovTop.HypothesesXH) : CovolX :=
  GlobalTheory.T.covolume_of_height hS hX (GlobalTheory.T.exists_ch2Const_of_prints (GlobalTheory.CovTop.hypotheses3_of_slim hS hX.cube).2.1.base hX.y.alt hX.arr)

example : Slim → HypothesesXH → CovolX := covolX_of_slim₂

end GlobalTheory.CovTop
