import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)
