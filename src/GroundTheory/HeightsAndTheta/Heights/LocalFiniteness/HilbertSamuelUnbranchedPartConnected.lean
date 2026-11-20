import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadIsoLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_DivCycleHomLoc.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.NumbersDVR.ResidualDisjoint.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction

theorem GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadIsoLoc : GroundTheory.Heights₂.Heights.Model.SpreadIsoLoc.Statement :=
  @GroundTheory.Heights₂.Heights.Model.SpreadIsoLoc.proof GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomLoc GroundTheory.Heights₂.Heights.AutoClose.Model_SpreadHomInjLoc

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeEuclMass.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeCollarMass GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass
