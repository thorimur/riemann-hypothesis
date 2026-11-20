import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Y : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t' : SAB H Y) (f : Z ⟶ Y) (_ : SABMap t t' f) (N : ℕ) (_ : GlobalTheory.LN.AmpFrames t.G t.PP.L N), 0 < N → IsNormalScheme Z → Flat z → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsProper f → IsFinite f := by
  first | exact @GlobalTheory.FrameFinite.isFinite_of_ampFrames | exact GlobalTheory.FrameFinite.isFinite_of_ampFrames | (intros; apply GlobalTheory.FrameFinite.isFinite_of_ampFrames <;> assumption)
