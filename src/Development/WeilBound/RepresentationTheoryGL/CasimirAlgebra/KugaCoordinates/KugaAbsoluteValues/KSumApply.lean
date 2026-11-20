import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
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

noncomputable section

open Fin Function

namespace PositivityTheory.Rg.Cz

section
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

def kLop (T : P →ₗ[ℝ] Module.End ℂ M) : P →ₗ[ℝ] M →ₗ[ℝ] M where
  toFun X := (T X).restrictScalars ℝ
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp

def kPre (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P →ₗ[ℝ] P [⋀^Fin m]→ₗ[ℝ] M where
  toFun X := (kLop T X).compAlternatingMap η
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp

def kD (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M) :
    P [⋀^Fin (m + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin (kPre T η)

theorem kD_apply (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (v : Fin (m + 1) → P) :
    kD T η v = ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • T (v i) (η (i.removeNth v)) := by
  simp [kD, AlternatingMap.alternatizeUncurryFin_apply, kPre, kLop]

theorem kSum_apply {N : Type} [AddCommGroup N] [Module ℝ N] {ι β : Type} (s : Finset β)
    (F : β → P [⋀^ι]→ₗ[ℝ] N) (v : ι → P) : (∑ i ∈ s, F i) v = ∑ i ∈ s, F i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

def kDel (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) : P [⋀^Fin n]→ₗ[ℝ] M :=
  ∑ i, (kLop T (b i)).compAlternatingMap (θ.curryLeft (b i))

theorem kDel_apply (T : P →ₗ[ℝ] Module.End ℂ M) {β : Type} [Fintype β] (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (v : Fin n → P) :
    kDel T b θ v = ∑ i, T (b i) (θ (Matrix.vecCons (b i) v)) := by
  unfold kDel
  rw [kSum_apply]
  rfl

def kIp (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) {β : Type} [Fintype β] (b : β → P) {m : ℕ}
    (η θ : P [⋀^Fin m]→ₗ[ℝ] M) : ℂ :=
  ∑ I : Fin m → β, B (η (b ∘ I)) (θ (b ∘ I))

end

end PositivityTheory.Rg.Cz

end
