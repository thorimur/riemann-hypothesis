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
import Mathlib.RepresentationTheory.Basic
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

theorem UpperTheory.Reformulated.B.Yhd2.main :
    ∀ {G M : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
      [inst_4 : AddCommGroup M] [inst_5 : _root_.Module ℂ M] (ρ : Representation ℂ G M) (x : M),
      IsOpen {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x} →
        (Set.range fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x).Countable := by
  intro G M _ _ _ _ _ _ ρ x hS
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  apply (hDc.image (fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x)).mono
  rintro _ ⟨g, rfl⟩
  have hU : IsOpen ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}) :=
    hS.preimage (continuous_const.mul continuous_id)
  have hne : ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}).Nonempty :=
    ⟨g, by simp⟩
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU hne
  refine ⟨d, hdD, ?_⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hdU
  have : d = g * (g⁻¹ * d) := by group
  simp only
  rw [this, map_mul, Module.End.mul_apply, hdU]
