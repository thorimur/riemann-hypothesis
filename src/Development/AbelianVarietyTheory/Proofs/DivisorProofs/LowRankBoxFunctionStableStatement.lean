import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStable
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_box_function_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | exact GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan <;> assumption)
