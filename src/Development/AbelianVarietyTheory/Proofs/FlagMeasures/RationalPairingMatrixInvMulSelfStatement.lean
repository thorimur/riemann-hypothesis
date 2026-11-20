import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPairingMatrixInvMulSelf
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPairingMatrix_inv_mul_self : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), G.Zh⁻¹ * G.Zh = 1 := by
  first | exact @GlobalTheory.HL.GFrames.Zh_inv_mul | exact GlobalTheory.HL.GFrames.Zh_inv_mul | (intros; apply GlobalTheory.HL.GFrames.Zh_inv_mul <;> assumption)
