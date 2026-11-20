import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import Mathlib.Analysis.CStarAlgebra.Classes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def NormalModelProjectionLocallyInjective.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ U ∈ 𝓝 w, Set.InjOn IndefiniteRowSideFullHecke.ComplexSets.firstCoords (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U)

end

end GroundTheory.Heights₂.Heights
