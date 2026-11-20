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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n

variable {T : Type} (r : T → ℕ) (n : ℕ)

def letMat (R : Type) [CommRing R] (σ : T) :
    Matrix (Fin (r σ)) (Fin n) (MvPolynomial (Letter T r n) R) :=
  fun a b => X ⟨σ, a, b⟩

variable (k : Type) [Field k]

def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)

def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')

def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ

def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P

def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i

def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}

def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}

end Formalism.L2.Pj
