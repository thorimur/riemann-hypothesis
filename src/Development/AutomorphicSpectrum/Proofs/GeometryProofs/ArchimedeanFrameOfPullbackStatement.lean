import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_frame_of_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm <;> assumption)
