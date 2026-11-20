import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_res | exact GlobalTheory.LogPair.isEtCoord_res | (intros; apply GlobalTheory.LogPair.isEtCoord_res <;> assumption)
