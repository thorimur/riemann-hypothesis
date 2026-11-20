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

noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section Cayley

variable (n : ℕ) (R : Type*) [CommRing R]

abbrev cayDet : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

def cayMono (σ : Equiv.Perm (Fin n)) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ((List.finRange n).map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod

def cayOp : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ)) • cayMono n R σ

def CayleyStatement : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] (s : ℕ),
    cayOp n R (cayDet n R ^ s) = (∏ k ∈ range n, (s + k)) • cayDet n R ^ (s - 1)

end Cayley

section Tests

variable (R : Type*) [CommRing R]

end Tests

section HW

variable {ν : ℕ} {ι : Type*}

def rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) :
    MvPolynomial (Fin ν × ι) ℂ →ₐ[ℂ] MvPolynomial (Fin ν × ι) ℂ :=
  aeval fun p => ∑ l, C (g l p.1) * X (l, p.2)

open scoped Classical in

def fischer (P Q : MvPolynomial (Fin ν × ι) ℂ) : ℂ :=
  ∑ A ∈ P.support ∪ Q.support,
    coeff A P * starRingEnd ℂ (coeff A Q) * ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

def IsUpperUnitri (g : Matrix (Fin ν) (Fin ν) ℂ) : Prop :=
  (∀ i, g i i = 1) ∧ ∀ i j, j < i → g i j = 0

def IsGLStable (N : Submodule ℂ (MvPolynomial (Fin ν × ι) ℂ)) : Prop :=
  ∀ g : GL (Fin ν) ℂ, ∀ P ∈ N, rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) P ∈ N

def unipFixed (N : Submodule ℂ (MvPolynomial (Fin ν × ι) ℂ)) : Set (MvPolynomial (Fin ν × ι) ℂ) :=
  {F | F ∈ N ∧ ∀ g, IsUpperUnitri g → rowSubst g F = F}

def FischerAdjointStatement : Prop :=
  ∀ (ν : ℕ) (ι : Type) (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ),
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q)

def HWFixedStatement : Prop :=
  ∀ (ν : ℕ) (ι : Type) (N : Submodule ℂ (MvPolynomial (Fin ν × ι) ℂ)),
    FiniteDimensional ℂ N → N ≠ ⊥ → IsGLStable N → ∃ F ∈ unipFixed N, F ≠ 0

def HWSpanStatement : Prop :=
  ∀ (ν : ℕ) (ι : Type) (M : Submodule ℂ (MvPolynomial (Fin ν × ι) ℂ)),
    FiniteDimensional ℂ M → IsGLStable M →
    (∃ v₀ : MvPolynomial (Fin ν × ι) ℂ, v₀ ≠ 0 ∧
      unipFixed M = ((ℂ ∙ v₀ : Submodule ℂ (MvPolynomial (Fin ν × ι) ℂ)) : Set _)) →
    ∀ v ∈ M, v ≠ 0 →
      Submodule.span ℂ (Set.range fun g : GL (Fin ν) ℂ => rowSubst (g : Matrix _ _ ℂ) v) = M

end HW

end ReciprocityTheory.PGsh
