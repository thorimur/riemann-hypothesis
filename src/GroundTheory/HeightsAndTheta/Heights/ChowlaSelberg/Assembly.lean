import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassEpstein
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PZetaFactor
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PDeltaEta
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhTau
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhScale
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PKroneckerLimit
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PKroneckerSplit
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPowerIntegral
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PShiftedSumIntegral
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PCotangentSum
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLogEta
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PGammaZetaLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

theorem KroneckerLimit.full : KroneckerLimit.Statement :=
  KroneckerLimit.proof KroneckerSplit.proof PowerIntegral.proof ShiftedSumIntegral.proof
    CotangentSum.proof LogEta.proof GammaZetaLimit.proof

theorem PhTau.full : PhTau.Statement :=
  PhTau.proof DeltaEta.proof

theorem ClassMean.full {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) : ClassMean.Statement S :=
  ClassMean.proof S KroneckerLimit.full (ClassEpstein.proof S) (ZetaFactor.proof S) PhTau.full
    PhScale.proof

section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
