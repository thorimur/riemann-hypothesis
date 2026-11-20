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

theorem UpperTheory.map_involution_eq_self :
    ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ] (ι : X → X) (c : NNReal), Measurable ι → (∀ᵐ x ∂μ, ι (ι x) = x) → μ.map ι = c • μ → μ.map ι = μ := by
  intro X _ μ _ ι c hι hinv hc
  by_cases h0 : μ = 0
  · subst h0
    simp
  have h1 : (μ.map ι).map ι = μ := by
    rw [MeasureTheory.Measure.map_map hι hι]
    have h : (ι ∘ ι) =ᵐ[μ] id := hinv
    rw [MeasureTheory.Measure.map_congr h, MeasureTheory.Measure.map_id]
  have h2 : (c * c) • μ = μ := by
    calc (c * c) • μ = c • (c • μ) := mul_smul c c μ
      _ = c • μ.map ι := by rw [hc]
      _ = (c • μ).map ι := (MeasureTheory.Measure.map_smul c μ ι).symm
      _ = (μ.map ι).map ι := by rw [hc]
      _ = μ := h1
  obtain ⟨s, -, -, hs0, hs1⟩ :=
    MeasureTheory.Measure.exists_subset_measure_lt_top (μ := μ) (s := Set.univ) (r := 0)
      MeasurableSet.univ (MeasureTheory.Measure.measure_univ_pos.mpr h0)
  have h3 : ((c * c : NNReal) : ENNReal) * μ s = 1 * μ s := by
    have h := congrArg (fun ν : MeasureTheory.Measure X => ν s) h2
    simpa [ENNReal.smul_def] using h
  have h4 : ((c * c : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hs0.ne' hs1.ne).mp h3
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have h : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have hc0 : (0 : ℝ) ≤ c := c.2
    have h' : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast h'
  rw [hc, h6, one_smul]
