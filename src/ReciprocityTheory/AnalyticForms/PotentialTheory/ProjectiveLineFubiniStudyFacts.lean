import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurve
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

namespace ReciprocityTheory.AnForm.M

theorem layerM :
    IsPotentialAddStatement ∧
    IsPotentialZsmulStatement ∧
    IsPotentialRsmulStatement ∧
    IsPotentialPullbackStatement ∧
    IsPshAddStatement ∧
    IsPshRsmulStatement ∧
    PshShiftStatement ∧
    RegularAtlasStatement ∧
    SNCInducedAtlasStatement ∧
    ExistsPartitionStatement ∧
    LocDensBaseStatement ∧
    LocDensContStatement ∧
    LocDensChartStatement ∧
    IntegralWithIndepStatement ∧
    MIntEqStatement ∧
    MIntAtlasIndepStatement ∧
    MIntegrableContStatement ∧
    MIntSymmStatement ∧
    MIntAddStatement ∧
    MIntZsmulStatement ∧
    MIntRsmulStatement ∧
    MIntLinearStatement ∧
    MIntNonnegStatement ∧
    MIntMeasureStatement ∧
    MaMeasureStatement ∧
    MaMeasureMonoStatement ∧
    LocDensPosStatement ∧
    AnalyticNullStatement ∧
    MIntCongrNullStatement ∧
    StokesStatement ∧
    ByPartsSymmStatement ∧
    ByPartsNonposStatement ∧
    MassIndepStatement ∧
    LogNormIntegrableStatement ∧
    PoincareLelongCurveStatement ∧
    PoincareLelongStatement ∧
    PushForwardStatement ∧
    LocDensPullbackStatement ∧
    RankDropStatement ∧
    DegreeFormulaStatement ∧
    DegreeFormulaIntStatement :=
  ⟨isPotentialAdd,
   isPotentialZsmul,
   isPotentialRsmul,
   isPotentialPullback,
   isPshAdd,
   isPshRsmul,
   pshShift,
   regularAtlas,
   sncInducedAtlas,
   existsPartition,
   locDensBase,
   locDensCont,
   locDensChart,
   integralWithIndep,
   mIntEq,
   mIntAtlasIndep,
   mIntegrableCont,
   mIntSymm,
   mIntAdd,
   mIntZsmul,
   mIntRsmul,
   mIntLinear,
   mIntNonneg,
   mIntMeasure,
   maMeasure_thm,
   maMeasureMono,
   locDensPos,
   analyticNull,
   mIntCongrNull,
   stokes,
   byPartsSymm,
   byPartsNonpos,
   massIndep,
   logNormIntegrable,
   plCurve,
   poincareLelong,
   pushForward,
   locDensPullback,
   rankDrop,
   degreeFormula,
   degreeFormulaInt⟩

theorem projectiveLine_fubiniStudy_facts :
    IsPotential p1 fsPot ∧ IsPsh p1 fsPot ∧ Nonempty (ChartPartition p1) ∧
      IsSection p1 fsPot projectiveLinePairSection ∧ IsSNC p1 fsPot projectiveLinePairSection ![1] ![{OnePoint.infty}] :=
  ⟨projLine_isSmoothPotential, projLine_isPlurisubharmonic, projLine_partition, projLine_isHolomorphicSection, projLine_isSimpleNormalCrossing⟩

end ReciprocityTheory.AnForm.M
