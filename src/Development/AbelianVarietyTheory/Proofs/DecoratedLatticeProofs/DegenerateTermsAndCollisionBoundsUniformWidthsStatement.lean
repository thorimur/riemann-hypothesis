import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidths
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths : (∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ ∀ c : ℝ, On {c} CollS := by
  first | exact @GlobalTheory.Core.Deg.degenerate_and_collisions_uncond | exact GlobalTheory.Core.Deg.degenerate_and_collisions_uncond | (intros; apply GlobalTheory.Core.Deg.degenerate_and_collisions_uncond <;> assumption)
