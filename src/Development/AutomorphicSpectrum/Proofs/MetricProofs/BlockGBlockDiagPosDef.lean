import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBlockpos
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem blockG_isBlockDiag_posDef :
    ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef →
      IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef :=
  PositivityTheory.Xgp.t_c_bm_exists_blockpos

end GlobalTheory.CompanionTheory.Ar.PB.BMx
