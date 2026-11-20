import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open MeasureTheory

theorem UpperTheory.ConvolutionTheory.K.presOfOrder :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (e : G ≃ₜ* G) (m : ℕ),
      0 < m → (∀ g, (⇑e)^[m] g = g) → MeasurePreserving e μ μ := by
  intro G _ _ _ _ _ _ _ _ μ _ e m hm he
  have hme : Measurable (e : G → G) := e.continuous.measurable
  haveI : (Measure.map e μ).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e μ = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hit : ∀ k : ℕ, Measure.map ((⇑e)^[k]) μ = c ^ k • μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', ← Measure.map_map hme (hme.iterate k), ih, Measure.map_smul, hc, smul_smul, pow_succ]
  have h1 : μ = c ^ m • μ := by
    rw [← hit m, show (⇑e)^[m] = id from funext he, Measure.map_id]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hK1 : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (1 : ENNReal) * μ K = ((c ^ m : NNReal) : ENNReal) * μ K := by
    rw [one_mul]
    conv_lhs => rw [h1]
    rfl
  have h3 : c ^ m = 1 := by
    have := (ENNReal.mul_left_inj hK0 hK1).1 h2
    exact_mod_cast this.symm
  have h4 : c = 1 := (pow_eq_one_iff_of_nonneg (zero_le) hm.ne').1 h3
  exact ⟨hme, by rw [hc, h4, one_smul]⟩
