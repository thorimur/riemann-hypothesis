import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.landherr_and_landherrSt :
    _root_.GlobalTheory.Published.Landherr ∧ _root_.GlobalTheory.Published.LandherrSt :=
  ⟨_root_.GlobalTheory.LocalQuad.landherr_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt,
    _root_.GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt _root_.GlobalTheory.QNorm.hasseNormSt⟩

end GlobalTheory.QNorm
