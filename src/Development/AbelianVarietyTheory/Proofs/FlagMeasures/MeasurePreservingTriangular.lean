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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.TriShift

section General
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι]

open ValuativeRel MeasureTheory ComplexConjugate in
open scoped ComplexOrder in
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι] in
private lemma measurePreserving_update_add_of_indep [DecidableEq ι] (i : ι)
    (g : (ι → G) → G) (hg : Measurable g)
    (hgi : ∀ x y : ι → G, (∀ j, j ≠ i → x j = y j) → g x = g y) :
    MeasurePreserving (fun x : ι → G => Function.update x i (x i + g x))
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  let p : ι → Prop := fun j => j ≠ i
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => G) p
  have he : MeasurePreserving e (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p
  let c : ({j // p j} → G) → ({j // ¬ p j} → G) := fun y _ => g (e.symm (y, 0))
  have hc : Measurable c :=
    measurable_pi_lambda _ fun _ =>
      hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hT : MeasurePreserving
      (fun q : ({j // p j} → G) × ({j // ¬ p j} → G) => (id q.1, q.2 + c q.1))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ))
      ((Measure.pi fun _ : {j // p j} => μ).prod (Measure.pi fun _ : {j // ¬ p j} => μ)) :=
    (MeasurePreserving.id _).skew_product (g := fun y z => z + c y)
      (measurable_snd.add (hc.comp measurable_fst))
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self _ _)
  have hcomp := (MeasurePreserving.symm e he).comp (hT.comp he)
  convert hcomp using 1
  funext x j
  by_cases hj : j = i
  · subst hj
    simp [e, c, p]
    exact hgi _ _ fun k hk => by simp [hk]
  · simp [e, c, p, hj]

open ValuativeRel MeasureTheory ComplexConjugate in
open scoped ComplexOrder in
variable {G : Type} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsAddRightInvariant]
  {ι : Type} [Fintype ι] in

theorem _root_.GlobalTheory.SgLoc.TriShift.measurePreserving_triangular (rk : ι → ℕ) (f : ι → (ι → G) → G)
    (hf : ∀ i, Measurable (f i))
    (hd : ∀ i x y, (∀ j, rk j < rk i → x j = y j) → f i x = f i y) :
    MeasurePreserving (fun (x : ι → G) i => x i + f i x) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
  classical
  let Φ : Finset ι → (ι → G) → ι → G := fun s x j => if j ∈ s then x j + f j x else x j
  have hΦ : ∀ s, MeasurePreserving (Φ s) (Measure.pi fun _ : ι => μ)
      (Measure.pi fun _ : ι => μ) := by
    intro s
    induction s using Finset.induction_on_max_value rk with
    | empty =>
      convert MeasurePreserving.id (Measure.pi fun _ : ι => μ) using 1
      funext x j
      simp [Φ]
    | insert a s ha hmax ih =>
      have hstep := measurePreserving_update_add_of_indep μ a (f a) (hf a)
        fun x y hxy => hd a x y fun j hj => hxy j (by rintro rfl; exact lt_irrefl _ hj)
      convert ih.comp hstep using 1
      funext x j
      by_cases hja : j = a
      · subst hja
        simp [Φ, ha]
      · by_cases hjs : j ∈ s
        · have hf' : f j (Function.update x a (x a + f a x)) = f j x :=
            hd j _ _ fun k hk => by
              have hka : k ≠ a := by
                rintro rfl
                exact absurd (hmax j hjs) (not_le.2 hk)
              simp [hka]
          simp [Φ, hja, hjs, hf']
        · simp [Φ, hja, hjs]
  convert hΦ Finset.univ using 1
  funext x j
  simp [Φ]

end General

end GlobalTheory.SgLoc.TriShift
