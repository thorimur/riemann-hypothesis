import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual

namespace UpperTheory.Gal.Int.Inp

structure Inp : Prop where
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  ac : GlobalTheory.Published.ArthurClozelStrongTC
  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove
  alg : GlobalTheory.Published.AlgebraicCharacterWD
  pst : GlobalTheory.Published.DeRhamPotSemistable

end UpperTheory.Gal.Int.Inp
