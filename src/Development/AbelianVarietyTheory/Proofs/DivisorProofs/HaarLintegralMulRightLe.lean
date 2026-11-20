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
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Monotonicity.Lemmas
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

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GlobalTheory.HaarRightTranslate

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem map_mul_right_eq_modular (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    map (· * g) μ = modularCharacterFun g • μ := by
  rw [modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul _ μ

theorem modular_bdd_on_compact {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ≥0, ∀ v ∈ V, modularCharacterFun v ≤ M := by
  set μ : Measure H := haar
  have K : PositiveCompacts H := Classical.arbitrary _
  set A : Set H := closure (K : Set H) with hA
  have hAc : IsCompact A := K.isCompact.closure
  have hAm : MeasurableSet A := isClosed_closure.measurableSet
  have hpos : μ A ≠ 0 :=
    (measure_pos_of_nonempty_interior _
      (K.interior_nonempty.mono (interior_mono subset_closure))).ne'
  have hfin : μ A ≠ ∞ := hAc.measure_lt_top.ne
  have hB : IsCompact (A * V⁻¹) := hAc.mul hV.inv
  have hBfin : μ (A * V⁻¹) ≠ ∞ := hB.measure_lt_top.ne
  refine ⟨(μ (A * V⁻¹) / μ A).toNNReal, fun v hv => ?_⟩
  have h1 : (modularCharacterFun v : ℝ≥0∞) * μ A ≤ μ (A * V⁻¹) := by
    have h := congrArg (fun ρ : Measure H => ρ A) (map_mul_right_eq_modular μ v)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← h, map_apply (measurable_mul_const _) hAm]
    refine measure_mono fun x hx => ?_
    exact ⟨x * v, hx, v⁻¹, by simpa using hv, by simp⟩
  have h2 : (modularCharacterFun v : ℝ≥0∞) ≤ μ (A * V⁻¹) / μ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 h1
  have hne : μ (A * V⁻¹) / μ A ≠ ∞ := ENNReal.div_ne_top hBfin hpos
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
  exact h2

end HaarRightTranslate

theorem haar_lintegral_mul_right_le :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
      [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H),
      μ.IsHaarMeasure → ∀ K : Set H, IsCompact K → ∃ B : NNReal, ∀ y ∈ K, ∀ φ : H → ENNReal,
        Measurable φ → ∫⁻ x, φ (x * y) ∂μ ≤ B * ∫⁻ x, φ x ∂μ := by
  intro H _ _ _ _ _ _ _ _ μ hμ K hK
  obtain ⟨M, hM⟩ := HaarRightTranslate.modular_bdd_on_compact hK
  refine ⟨M, fun y hy φ hφ => ?_⟩
  have e : ∫⁻ x, φ (x * y) ∂μ = ∫⁻ x, φ x ∂(map (· * y) μ) :=
    (lintegral_map hφ (measurable_mul_const y)).symm
  rw [e, HaarRightTranslate.map_mul_right_eq_modular μ y, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul]
  gcongr
  exact_mod_cast hM y hy

end GlobalTheory
