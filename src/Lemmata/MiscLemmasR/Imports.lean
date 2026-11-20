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
import Mathlib.Topology.Sheaves.Init

namespace Bl.ThirdBlockLemmaC

noncomputable def goal1 :
  {K : Type} →   [inst : Field K] →     [NumberField K] →       RingHom K K → Submodule (NumberField.RingOfIntegers K) K → Submodule (NumberField.RingOfIntegers K) K := @fun K _ _ σ M =>
  { carrier := σ ⁻¹' (M : Set K)
    add_mem' := fun {x y} hx hy => by
      simp only [Set.mem_preimage, map_add, SetLike.mem_coe] at *
      exact M.add_mem hx hy
    zero_mem' := by
      simp only [Set.mem_preimage, map_zero, SetLike.mem_coe]
      exact M.zero_mem
    smul_mem' := fun r x hx => by
      simp only [Set.mem_preimage, SetLike.mem_coe] at *
      have hr : IsIntegral ℤ (σ (r : K)) := (NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom
      have h : σ (r • x) = (⟨σ (r : K), hr⟩ : NumberField.RingOfIntegers K) • σ x := by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        rfl
      rw [h]
      exact M.smul_mem _ hx }

end Bl.ThirdBlockLemmaC
