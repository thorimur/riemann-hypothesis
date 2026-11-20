import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIso
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ ξ : Fˣ →* ℂˣ, GlobalTheory.SplitWeil.IsTame ξ → ∃ χ : (ZMod g)ˣ →* ℂˣ, TamePart (ξ.comp (Units.map e.toMonoidHom)) χ := by
  first | exact @GlobalTheory.TameRead.exists_tamePart | exact GlobalTheory.TameRead.exists_tamePart | (intros; apply GlobalTheory.TameRead.exists_tamePart <;> assumption)
