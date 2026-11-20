import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_subgroup_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) → IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp <;> assumption)
