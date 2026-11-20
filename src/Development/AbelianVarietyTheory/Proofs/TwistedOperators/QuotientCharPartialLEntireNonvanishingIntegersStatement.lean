import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  first | exact @GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero <;> assumption)
