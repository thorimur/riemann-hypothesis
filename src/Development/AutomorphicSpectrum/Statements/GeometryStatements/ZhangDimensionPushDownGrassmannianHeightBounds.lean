import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace Prov

def HS : Prop :=
  SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticIntersectionNonneg ∧ ArithmeticVolumeLowerBound ∧ BirationalPullbackPushforwardFormula ∧ ArithmeticHilbertSamuelUpperBound ∧ ArithmeticHilbertSamuelUpperBoundNumberField ∧
    HilbertSamuel.G3.Statement ∧ HilbertSamuel.ArithmeticVolumeMultiplicative.Statement

def An : Prop :=
  ReciprocityTheory.AnForm.P.TailBoundStatement ∧ ReciprocityTheory.AnForm.P.ConvergenceStatement ∧
    ReciprocityTheory.AnForm.P.ConvergenceSignedStatement ∧ ReciprocityTheory.AnForm.P.ConvergenceRateStatement ∧
    ReciprocityTheory.AnForm.P.UnifIntStatement ∧ ReciprocityTheory.AnForm.P.PullbackStatement ∧ ReciprocityTheory.AnForm.P.RegGlobalStatement

def ZhangDimensionPushDownGrassmannianHeightBounds : Prop :=
  ZhangLowerX.Statement ∧ DimX.Statement ∧ True ∧ PushDown.Statement ∧ GrassmannianHeightZTwo.Statement

abbrev LemmaS := @SlopeBoundSt

def All : Prop := HS ∧ An ∧ ZhangDimensionPushDownGrassmannianHeightBounds ∧ LemmaS

end Prov

end GlobalTheory.CompanionTheory.Ar
