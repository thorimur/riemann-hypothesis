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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

def eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) where
  carrier := {u | ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u}
  add_mem' := by
    intro u v hu hv c
    rw [Matrix.mulVec_add, hu c, hv c, smul_add]
  zero_mem' := by intro c; simp
  smul_mem' := by
    intro a u hu c
    rw [Matrix.mulVec_smul, hu c, smul_comm]

theorem mem_eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ)
    (u : Fin g → ℂ) : u ∈ eigSp φ τ ↔ ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u := Iff.rfl

end GlobalTheory.UPel.HT.LieType
