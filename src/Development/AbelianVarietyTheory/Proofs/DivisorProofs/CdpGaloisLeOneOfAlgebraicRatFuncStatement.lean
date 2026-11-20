import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CdpGaloisLeOneOfAlgebraicRatFunc
open GroundTheory.ProfCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cdp_galois_le_one_of_isAlgebraic_ratFunc : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (p : ℕ), p.Prime → GroundTheory.ProfCoh.cdp p (Ω ≃ₐ[K] Ω) ≤ 1 := by
  first | (exact @GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (exact GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc) | (intros; apply GlobalTheory.TsenCD.cdp_galois_le_one_of_algebraic_ratFunc  <;> assumption)
