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
import Mathlib.Topology.Sheaves.Presheaf

noncomputable def UpperTheory.Reformulated.B.Qh31.vR :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → K → WithTop ℝ :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (x : K) ↦
      WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ)) ((v : K → WithTop ℚ) x)

noncomputable def UpperTheory.Reformulated.B.Qh31.vge :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → ℝ → K → Prop :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) ↦ (↑a : WithTop ℝ) ≤ UpperTheory.Reformulated.B.Qh31.vR v x

private theorem UpperTheory.Reformulated.B.Qh31.map_cast_mono :
    Monotone (WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ))) :=
  Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)

theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by
  intro K _ v ι a s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h
  · intro x y hx hy
    unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *
    rcases min_le_iff.mp (v.map_add x y) with hxy | hxy
    · exact hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
    · exact hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
  · unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR
    rw [v.map_zero, WithTop.map_top]
    exact le_top
