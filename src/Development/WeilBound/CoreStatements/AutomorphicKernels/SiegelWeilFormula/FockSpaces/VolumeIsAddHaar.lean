import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section

open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.KFock

theorem volume_isAddHaar (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  have h2 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : SigmaFinite (volume : Measure (Fin n → ℂ)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]

theorem measure_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ c : NNReal, 0 < c ∧ ν = c • Measure.map Φ (la.prod mu) := by
  have hmap : (Measure.map Φ (la.prod mu)).IsAddHaarMeasure :=
    Φ.toAddEquiv.isAddHaarMeasure_map (la.prod mu) Φ.continuous Φ.symm.continuous
  refine ⟨Measure.addHaarScalarFactor ν (Measure.map Φ (la.prod mu)),
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul ν _

theorem integral_split (ν : Measure G) [ν.IsAddHaarMeasure] (la : Measure H) [la.IsAddHaarMeasure]
    (mu : Measure K) [mu.IsAddHaarMeasure] (Φ : H × K ≃ₜ+ G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G → ℂ, ∫ x, g x ∂ν = C * ∫ p, g (Φ p) ∂(la.prod mu) := by
  obtain ⟨c, hc, hν⟩ := measure_split ν la mu Φ
  refine ⟨c, by exact_mod_cast hc, fun g => ?_⟩
  have hm := integral_map_equiv (μ := la.prod mu) (Φ.toHomeomorph.toMeasurableEquiv) g
  rw [hν, integral_smul_nnreal_measure]
  erw [hm]
  simp [NNReal.smul_def, Complex.real_smul]
  exact Or.inl rfl

end PositivityTheory.SiegelWeilFormula.KFock

end
