import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
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
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
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

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℤ

def slz (k : ℕ) (δ : M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
    f (ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))))

def LRep (L : ℕ) (Δ : Set M2) {ι : Type} (β : ι → M2) : Prop :=
  Set.BijOn (fun p : Gamma0 L × ι => ((p.1 : SL(2, ℤ)) : M2) * β p.2) Set.univ Δ

def RRep (L : ℕ) (Δ : Set M2) {κ : Type} (α : κ → M2) : Prop :=
  Set.BijOn (fun p : κ × Gamma0 L => α p.1 * ((p.2 : SL(2, ℤ)) : M2)) Set.univ Δ

def hsum (k : ℕ) (ε : ℤ → ℂ) {ι : Type} [Fintype ι] (β : ι → M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ i, ε (β i 0 0) * slz k (β i) f τ

def DT (L q : ℕ) : Set M2 := {δ | δ.det = q ∧ (L : ℤ) ∣ δ 1 0}

def DU (L l : ℕ) : Set M2 := {δ | δ.det = l ∧ (L : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0}

def repU (q : ℕ) (j : Fin q) : M2 := !![1, (j : ℕ); 0, q]

def repT (q : ℕ) : Option (Fin q) → M2
  | some j => repU q j
  | none => !![q, 0; 0, 1]

def repL (L q : ℕ) : Option (Fin q) → M2
  | some j => !![q, 0; L * (j : ℕ), 1]
  | none => !![1, 0; 0, q]

def Mod (F : ℍ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)

def latF (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) : ℤ × ℤ → ℂ := fun x => if (L : ℤ) ∣ x.1 then b (x.1 / L) * φ (x.2 : ZMod L) else 0

def Kills (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) : Prop := ∀ x, ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) = 0

def strip : Set ℍ := {τ | 0 ≤ τ.re ∧ τ.re < 1}

end GlobalTheory.EisM

end
