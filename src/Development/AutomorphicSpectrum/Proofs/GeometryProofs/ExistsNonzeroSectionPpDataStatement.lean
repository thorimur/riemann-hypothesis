import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int <;> assumption)
