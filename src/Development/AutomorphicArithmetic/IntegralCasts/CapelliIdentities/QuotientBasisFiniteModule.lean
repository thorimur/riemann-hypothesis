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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.FiniteModuleImageInFiniteExtension.qb_fdmod :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {M : Type}
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (f : M →ₗ[ℤ_[l]] PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      FiniteDimensional ℚ_[l] ↥K ∧ ∀ (x : M), (f : M → PadicAlgCl l) x ∈ K := by
  intro l _ M _ _ hM f
  obtain ⟨S, hS⟩ := hM.fg_top
  have hfin : (f '' (S : Set M)).Finite := S.finite_toSet.image _
  haveI : Finite (f '' (S : Set M)) := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro x
    have hx : x ∈ Submodule.span ℤ_[l] (S : Set M) := by
      rw [hS]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]
      exact IntermediateField.smul_mem _ ha
