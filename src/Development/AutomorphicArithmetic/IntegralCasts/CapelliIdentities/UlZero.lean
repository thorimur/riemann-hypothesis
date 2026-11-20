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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.Rb1.Zc :
    {D N : Type} → [inst : Group D] → [TopologicalSpace D] → [inst_2 : AddCommGroup N] → Representation ℤ D N → Set (D → N) :=
    fun {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) ↦
      {z : D → N | IsLocallyConstant z ∧ ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)}

theorem UpperTheory.Reformulated.B.Rb1.ul_zero :
    ∀ {D N : Type} [inst : Group D] [inst_1 : TopologicalSpace D] [inst_2 : IsTopologicalGroup D] [inst_3 : AddCommGroup N]
      (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
        ∀ z ∈ UpperTheory.Reformulated.B.Rb1.Zc ρ, (∀ s ∈ I, z s = (0 : N)) → z φ = (0 : N) → ∀ (s : D), z s = (0 : N) := by
  intro D N _ _ _ _ ρ I φ hcl z hz hI hφ s
  have hlc : IsLocallyConstant z := hz.1
  have hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t) := hz.2
  have h1 : z 1 = 0 := by
    have h := hco 1 1
    rw [mul_one, map_one] at h
    simpa using h
  let K : Subgroup D :=
    { carrier := z ⁻¹' {0}
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = 0 := ha
        have hb' : z b = 0 := hb
        show z (a * b) = 0
        rw [hco, ha', hb', map_zero, add_zero]
      one_mem' := h1
      inv_mem' := by
        intro a ha
        have ha' : z a = 0 := ha
        show z a⁻¹ = 0
        have h := hco a⁻¹ a
        rw [inv_mul_cancel, h1, ha', map_zero, add_zero] at h
        exact h.symm }
  have hK : IsClosed (K : Set D) := hlc.isClosed_fiber 0
  have hle : I ⊔ Subgroup.zpowers φ ≤ K :=
    sup_le hI (by
      rw [Subgroup.zpowers_le]
      exact hφ)
  have htop : (⊤ : Subgroup D) ≤ K := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hK
  exact htop (Subgroup.mem_top s)
