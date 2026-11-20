import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_subgroups_closed_normal_cocompact' : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), IsClosed (flagN d : Set (GA D V)) ∧ ∀ M : Subgroup (GA D V), (M = centre d ∨ M = radX d ∨ ∃ j, M = Nfix d j) → M ≤ flagN d ∧ IsClosed (M : Set (GA D V)) ∧ (M.subgroupOf (flagN d)).Normal ∧ ∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ (GQ V).subgroupOf M, ∃ k ∈ K, m = γ * k := by
  first | exact @GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | exact GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact | (intros; apply GlobalTheory.Unf.FlagSub.flag_subgroups_closed_normal_cocompact <;> assumption)
