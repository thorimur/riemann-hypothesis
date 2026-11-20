import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  first | exact @GlobalTheory.GenFibreGen.exists_secs_generic | exact GlobalTheory.GenFibreGen.exists_secs_generic | (intros; apply GlobalTheory.GenFibreGen.exists_secs_generic <;> assumption)
