import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

open Matrix Complex
open scoped ComplexConjugate

namespace GlobalTheory.SW

noncomputable section

section Test

variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

def IntM (x : Matrix κ ι K) : Prop := ∀ k i, IsIntegral ℤ (x k i)

def HasLevel (R : ℕ) (φ : Matrix κ ι K → ℂ) : Prop :=
  (∀ x, φ x ≠ 0 → IntM ((R : K) • x)) ∧ ∀ x y, IntM y → φ (x + (R : K) • y) = φ x

def IsSB (φ : Matrix κ ι K → ℂ) : Prop := ∃ R : ℕ, 0 < R ∧ HasLevel R φ

def perSub (K κ ι : Type) [Field K] (R : ℕ) : AddSubgroup (Matrix κ ι K) :=
  AddSubgroup.closure {x | ∃ y : Matrix κ ι K, IntM y ∧ x = (R : K) • y}

def haarAt (R : ℕ) (φ : Matrix κ ι K → ℂ) : ℂ :=
  ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out

open Classical in

def haar (φ : Matrix κ ι K → ℂ) : ℂ := if h : IsSB φ then haarAt h.choose φ else 0

def ip (φ ψ : Matrix κ ι K → ℂ) : ℂ := haar fun x => φ x * conj (ψ x)

theorem isSB_zero : IsSB (0 : Matrix κ ι K → ℂ) := by
  refine ⟨1, Nat.one_pos, fun x hx => ?_, fun x y _ => rfl⟩
  exact absurd rfl hx

end Test

section Siegel

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

def Siegel (ι : Type) [Fintype ι] : Set (Matrix ι ι ℂ) := {τ | τ.IsSymm ∧ (τ.map Complex.im).PosDef}

def qv (v : ι → ℚ) : ι → ℂ := fun i => (v i : ℂ)

def thS (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) : ℂ :=
  ∑' x : Matrix κ ι ℚ, φ x *
    cexp (Real.pi * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))

def qm {α β : Type} (A : Matrix α β ℚ) : Matrix α β ℂ := A.map fun t => (t : ℂ)

def spDen (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (τ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  qm σ.toBlocks₂₁ * τ + qm σ.toBlocks₂₂

def spAct (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (τ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂) * (spDen σ τ)⁻¹

def TransS (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (φ ψ : Matrix κ ι ℚ → ℂ) : Prop :=
  ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ,
    thS ψ (spAct σ τ) (fun k => ζ k ᵥ* (spDen σ τ)⁻¹) =
      (spDen σ τ).det ^ (Fintype.card κ / 2) *
        cexp (Real.pi * I * ∑ k, ζ k ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ k) * thS φ τ ζ

def heisS (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ) : Matrix κ ι ℚ → ℂ := fun x =>
  φ (x - b) * cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))

theorem I_mem_siegel : (I • (1 : Matrix ι ι ℂ)) ∈ Siegel ι := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.IsSymm]
  · have him : (I • (1 : Matrix ι ι ℂ)).map Complex.im = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [him]
    exact Matrix.PosDef.one

end Siegel

end

end GlobalTheory.SW
