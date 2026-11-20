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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Finset

noncomputable section

namespace PI.RamBoundW

section Fil

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*} (δ : ι → Derivation R P P)

def apL : List ι → P →ₗ[R] P
  | [] => LinearMap.id
  | i :: T => apL T ∘ₗ (δ i).toLinearMap

@[simp] theorem apL_nil (M : P) : apL δ [] M = M := rfl

@[simp] theorem apL_cons (i : ι) (T : List ι) (M : P) : apL δ (i :: T) M = apL δ T (δ i M) := rfl

def Fil (a : ℕ) : Submodule R P where
  carrier := {M | ∀ T : List ι, a < T.length → apL δ T M = 0}
  add_mem' := by
    intro M N hM hN T hT
    rw [map_add, hM T hT, hN T hT, add_zero]
  zero_mem' := by
    intro T _
    exact map_zero _
  smul_mem' := by
    intro r M hM T hT
    rw [map_smul, hM T hT, smul_zero]

variable {δ}

end Fil

section Leib

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]

end Leib

end PI.RamBoundW
