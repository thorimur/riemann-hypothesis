import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection

namespace GlobalTheory.CovTop

structure Hypotheses₂ : Prop where
  p1 : GlobalTheory.Published.ToroidalCompactification
  p2 : GlobalTheory.Published.VolGe
  p3 : GlobalTheory.Published.VolNef
  p4 : GlobalTheory.Published.ArCalc
  p5 : GlobalTheory.Published.AbelianDeRham
  p6 : GlobalTheory.Published.TamagawaSpecialUnitary
  p8 : GlobalTheory.Published.RayClassFieldSt
  p12 : GlobalTheory.Published.SemistableReductionSt
  p13 : GlobalTheory.Published.StrongApproxSU
  p14 : GlobalTheory.Published.GreenSeriesSt
  p16 : GlobalTheory.Published.MumfordProportionality
  p18 : GlobalTheory.Published.FinitenessOfHermitianClasses
  p19 : GlobalTheory.Published.LandherrSt
  p20 : GlobalTheory.Published.HasseNormSt
  p22 : GlobalTheory.Published.SemiAbelianHomExtension
  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove
  p25 : GlobalTheory.Published.principalPolarisationOneSection
  p26 : GlobalTheory.Published.AbMulNSt

end GlobalTheory.CovTop
