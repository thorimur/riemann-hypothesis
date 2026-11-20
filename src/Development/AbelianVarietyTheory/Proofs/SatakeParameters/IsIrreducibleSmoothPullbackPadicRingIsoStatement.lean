import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIso
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  first | exact @GlobalTheory.SerSys.irrSm_pullback | exact GlobalTheory.SerSys.irrSm_pullback | (intros; apply GlobalTheory.SerSys.irrSm_pullback <;> assumption)
