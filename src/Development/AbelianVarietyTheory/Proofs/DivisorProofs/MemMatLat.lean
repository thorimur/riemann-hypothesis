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

noncomputable section

namespace GlobalTheory.LatOrb

open Polynomial Matrix

variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]

def stdLat (n : ℕ) : Submodule O (Fin n → K) where
  carrier := {v | ∀ i, v i ∈ (algebraMap O K).range}
  add_mem' := by
    intro a b ha hb i
    exact Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun i => Subring.zero_mem _
  smul_mem' := by
    intro c v hv i
    obtain ⟨a, ha⟩ := hv i
    exact ⟨c * a, by simp [Algebra.smul_def, ha]⟩

def matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    Submodule O (Fin n → K) :=
  M.map ((Matrix.mulVecLin g).restrictScalars O)

def IsLatV {n : ℕ} (M : Submodule O (Fin n → K)) : Prop :=
  M.FG ∧ Submodule.span K (M : Set (Fin n → K)) = ⊤

def herm {n : ℕ} (σ : K →+* K) (x y : Fin n → K) : K := ∑ k, x k * σ (y k)

def SelfDual {n : ℕ} (σ : K →+* K) (M : Submodule O (Fin n → K)) : Prop :=
  ∀ y, y ∈ M ↔ ∀ x ∈ M, herm σ y x ∈ (algebraMap O K).range

variable {O}

theorem mem_stdLat {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range :=
  Iff.rfl

theorem mem_matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by
  simp [matLat]

theorem matLat_mul {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by
  ext v
  simp only [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b *ᵥ u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [Matrix.mulVec_mulVec]⟩

theorem matLat_one {n : ℕ} (M : Submodule O (Fin n → K)) : matLat O 1 M = M := by
  ext v
  simp [mem_matLat]

end GlobalTheory.LatOrb
