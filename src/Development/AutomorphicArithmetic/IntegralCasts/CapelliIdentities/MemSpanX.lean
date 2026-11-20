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
import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) →
      ∃ (g : σ → MvPowerSeries σ O), f = ∑ i : σ, MvPowerSeries.X i * g i := by
  intro O σ _ _ f hf
  classical
  have hex : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ i, m i ≠ 0 := by
    intro m hm
    by_contra h
    apply hm
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  choose c hc using hex
  let p : (σ →₀ ℕ) → σ → Prop := fun m i => ∃ hm : m ≠ 0, c m hm = i
  let g : σ → MvPowerSeries σ O := fun i n =>
    if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0
  have hg : ∀ i n, MvPowerSeries.coeff n (g i) =
      if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f
      else 0 := fun _ _ => rfl
  have key : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * g i) =
      if p m i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : Finsupp.single i 1 ≤ m
    · rw [if_pos h, one_mul, hg, tsub_add_cancel_of_le h]
    · rw [if_neg h, if_neg]
      rintro ⟨hm, hi⟩
      apply h
      rw [Finsupp.single_le_iff, ← hi]
      exact Nat.one_le_iff_ne_zero.mpr (hc m hm)
  refine ⟨g, ?_⟩
  ext m
  rw [map_sum]
  simp only [key]
  by_cases hm : m = 0
  · subst hm
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    simp
  · rw [Finset.sum_eq_single (c m hm)]
    · rw [if_pos ⟨hm, rfl⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
