import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBaseChangeLineDegree
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_base_change_line_degree : ∀ (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K''] [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] (m : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K' (Fin m → K')) (h'' : HermFam K'' (Fin m → K'')) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K'), Full L → IsBC h h' → IsBC h h'' → Full (latBC K'' L) ∧ deg h'' (lineLat (latBC K'' L) (fun i => algebraMap K' K'' (x i))) = deg h' (lineLat (latBC K' L) x) := by
  first | exact @GlobalTheory.LineBCTower.lineLat_deg_tower | exact GlobalTheory.LineBCTower.lineLat_deg_tower | (intros; apply GlobalTheory.LineBCTower.lineLat_deg_tower <;> assumption)
