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

theorem UpperTheory.isOpen_stabilizer_add_smul :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (a b : V) (z : ℂ),
        IsOpen {g : G | ρ g a = a} → IsOpen {g : G | ρ g b = b} → IsOpen {g : G | ρ g (a + z • b) = a + z • b} := by
  intro G V _ _ _ _ _ ρ a b z ha hb
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ρ g (a + z • b) = a + z • b := hg
  have hc : Continuous fun x : G => g⁻¹ * x := continuous_const.mul continuous_id
  have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b})) :=
    (ha.inter hb).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · simp
  · intro x hx
    have h1 : ρ (g⁻¹ * x) a = a := hx.1
    have h2 : ρ (g⁻¹ * x) b = b := hx.2
    have h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b := by
      rw [map_add, map_smul, h1, h2]
    have h4 : x = g * (g⁻¹ * x) := by group
    show ρ x (a + z • b) = a + z • b
    rw [h4, map_mul, Module.End.mul_apply, h3, hg']
