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

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SplitExtLat

variable {P G₁ : Type} [Group P] [Group G₁]

def splitMap (ι : G₁ →* P) (π : P →* G₁) : π.ker × G₁ → P := fun z => (z.1 : P) * ι z.2

def kerPart (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (p : P) : π.ker :=
  ⟨p * (ι (π p))⁻¹, by simp [MonoidHom.mem_ker, h]⟩

def splitEquiv (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ P where
  toFun := splitMap ι π
  invFun p := (kerPart ι π h p, π p)
  left_inv z := by
    obtain ⟨⟨m, hm⟩, u⟩ := z
    have hm' : π m = 1 := hm
    ext <;> simp [splitMap, kerPart, hm', h]
  right_inv p := by simp [splitMap, kerPart]

def splitHomeo [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ₜ P where
  toEquiv := splitEquiv ι π h
  continuous_toFun := by
    change Continuous fun z : π.ker × G₁ => (z.1 : P) * ι z.2
    fun_prop
  continuous_invFun := by
    change Continuous fun p => (kerPart ι π h p, π p)
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπ
    fun_prop

@[simp] theorem splitHomeo_apply [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) (z : π.ker × G₁) :
    splitHomeo ι π hι hπ h z = (z.1 : P) * ι z.2 := rfl

theorem mul_split (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (g : P) (m : π.ker) (u : G₁) :
    g * ((m : P) * ι u) =
      ((kerPart ι π h g * MulAut.conjNormal (ι (π g)) m : π.ker) : P) * ι (π g * u) := by
  simp only [kerPart, Subgroup.coe_mul, MulAut.conjNormal_apply, map_mul]
  group

theorem continuous_conj [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) :
    Continuous fun z : G₁ × π.ker => MulAut.conjNormal (ι z.1) z.2 := by
  refine Continuous.subtype_mk (f := fun z : G₁ × π.ker => ι z.1 * (z.2 : P) * (ι z.1)⁻¹) ?_ _
  fun_prop

end GlobalTheory.CompanionTheory.SplitExtLat
