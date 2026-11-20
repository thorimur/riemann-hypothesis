import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianFormPeriodMatrixNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_period_matrix_normal_form : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  first | exact @GlobalTheory.CompanionTheory.NForm.normal_form_gram | exact GlobalTheory.CompanionTheory.NForm.normal_form_gram | (intros; apply GlobalTheory.CompanionTheory.NForm.normal_form_gram <;> assumption)
