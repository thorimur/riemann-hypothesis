import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLeStatement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem dict_ptIdeal_injective {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Function.Injective (ptIdeal : MP ℤ m n → Ideal (Geo.MRing (Bk n))) := fun x y h =>
  (((GlobalTheory.T.specializes_iff_point_ideal_le m n x y).2 h.le).antisymm ((GlobalTheory.T.specializes_iff_point_ideal_le m n y x).2 h.ge)).eq

end GlobalTheory.CompanionTheory.MPDict
