import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

theorem lintegral_fin_prod : ∀ (m : ℕ) {α : Fin m → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i
  | 0, α, _, μ, _, f, _ => by
    simp
  | m + 1, α, _, μ, _, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove μ 0
    set g : α 0 × ((j : Fin m) → α (Fin.succAbove 0 j)) → ℝ≥0∞ :=
      fun z => f 0 z.1 * ∏ i : Fin m, f (Fin.succAbove 0 i) (z.2 i) with hg
    have key : ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ =
        ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove α 0 x) ∂Measure.pi μ := by
      congr 1
      funext x
      rw [Fin.prod_univ_succAbove _ 0]
      rfl
    have hpm : ∫⁻ b, g b ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
        (∫⁻ x, f 0 x ∂μ 0) * ∫⁻ y : (j : Fin m) → α (Fin.succAbove 0 j), ∏ i, f (Fin.succAbove 0 i) (y i)
          ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
      lintegral_prod_mul (f := f 0) (g := fun y : (j : Fin m) → α (Fin.succAbove 0 j) => ∏ i, f (Fin.succAbove 0 i) (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
    rw [key, hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove α 0).measurableEmbedding g, hpm,
      lintegral_fin_prod m (fun j => μ (Fin.succAbove 0 j)) (fun j => f (Fin.succAbove 0 j)) (fun j => hf _),
      Fin.prod_univ_succAbove _ 0]

theorem lintegral_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have h1 : ∀ g : (∀ i', α (e i')), ∏ i, f i ((MeasurableEquiv.piCongrLeft α e g) i) =
      ∏ i', f (e i') (g i') := by
    intro g
    rw [← Fintype.prod_equiv e (fun i' => f (e i') (MeasurableEquiv.piCongrLeft α e g (e i')))
      (fun i => f i (MeasurableEquiv.piCongrLeft α e g i)) (fun _ => rfl)]
    congr 1
    funext i'
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [h1]
  rw [lintegral_fin_prod _ (fun i' => μ (e i')) (fun i' => f (e i')) (fun i' => hf _)]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
