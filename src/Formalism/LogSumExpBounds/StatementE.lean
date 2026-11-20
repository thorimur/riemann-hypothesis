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
import Mathlib.Topology.Sheaves.Init

namespace Formalism.NuclearRankWeightBounds.E

section
variable {K : Type*} [CommRing K] [StarRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsHerm (h : V →ₗ[K] V →ₗ⋆[K] K) : Prop := ∀ v w, h w v = star (h v w)

def tau (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V) (v : V) : V :=
  v + h v x • u - h v u • x
end

def TauIsom : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v w, h (tau h x u v) (tau h x u w) = h v w

def TauInv : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v, tau h x (-u) (tau h x u v) = v ∧ tau h x u (tau h x (-u) v) = v

def TauComp : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x x' u : V),
    IsHerm h → h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    ∀ v, tau h x u (tau h x' (-u) v)
      = v + h v (x - x') • u - h v u • (x - x') + (h v u * h x' x) • u

def TauLattice : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (O : Subring K) (abelian₂ : AddSubgroup V) (x x' u : V),
    IsHerm h → (∀ a ∈ O, star a ∈ O) →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    x - x' ∈ abelian₂ → u ∈ abelian₂ → h x' x ∈ O →
    tau h x u '' (abelian₂ : Set V) = tau h x' u '' (abelian₂ : Set V)

def mass {C : Type*} [Fintype C] (wt : C → C → ℝ) (c : C) : ℝ := ∑ c', wt c c'

noncomputable def sway {C : Type*} [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (c : C) : ℂ :=
  (om c)⁻¹ * ∑ c', (wt c c' : ℂ) * om c'

def PhaseSum : Prop :=
  ∀ (C : Type) [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (C1 : Finset C) (m0 ep : ℝ),
    (∀ c, ‖om c‖ = 1) → (∀ c c', wt c c' = wt c' c) → (∀ c c', 0 ≤ wt c c') → 0 < m0 →
    (∀ c, c ∉ C1 → sway om wt c = (mass wt c : ℂ)) →
    (∀ c ∈ C1, |mass wt c - m0| ≤ ep * m0 ∧ ‖sway om wt c‖ ≤ ep * m0) →
    ‖∑ c ∈ C1, om c‖ ≤ 2 * ep * (C1.card : ℝ)

end Formalism.NuclearRankWeightBounds.E
