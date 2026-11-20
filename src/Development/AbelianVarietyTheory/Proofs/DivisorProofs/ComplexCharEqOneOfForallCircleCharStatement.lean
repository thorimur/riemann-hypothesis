import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleChar
import Formalism.LocalRingCardinality.DataHost

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_forall_circle_char_eq_one : ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G), (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  first | exact @GlobalTheory.complexChar_eq_one_of_forall_circleChar | exact GlobalTheory.complexChar_eq_one_of_forall_circleChar | (intros; apply GlobalTheory.complexChar_eq_one_of_forall_circleChar <;> assumption)
