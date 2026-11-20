import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem algPtLa_moduli : N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → AlgPtLa Xo c :=
  fun h E _ _ _ H Dw l Xo c hpq =>
    Formalism.L2.PjFree.algPtLa_of (GlobalTheory.T.xoNumPt_of_p_add_q_pos h E H Dw l Xo c hpq) GlobalTheory.T.numberField_finitePlace_completion_embedding

end GlobalTheory
