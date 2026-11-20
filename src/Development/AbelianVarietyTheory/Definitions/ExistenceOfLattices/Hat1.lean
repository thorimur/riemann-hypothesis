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
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

namespace GlobalTheory.AdLat

open NumberField IsDedekindDomain
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

abbrev RA : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

variable {E}

def fv {n : ℕ} (v : Fin n → E) : Fin n → RA F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

def hat {n : ℕ} (L : Set (Fin n → E)) : AddSubgroup (Fin n → RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L, z = fun i => a ⊗ₜ x i}

def hat1 (J : Set E) : AddSubgroup (RA F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ J, z = a ⊗ₜ x}

def latOf {n : ℕ} (g : Matrix (Fin n) (Fin n) (RA F E)) (L : Set (Fin n → E)) : Set (Fin n → E) :=
  {v | fv F v ∈ g.mulVec '' (hat F L : Set (Fin n → RA F E))}

variable {F}

def sg (A : Type) [CommRing A] [Algebra F A] (c : E ≃ₐ[F] E) : A ⊗[F] E →ₐ[F] A ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id F A) (c : E →ₐ[F] E)

def hermA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) : RA F E :=
  ∑ a, ∑ b, x a * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G a b) * sg (FiniteAdeleRing (𝓞 F) F) c (y b)

end GlobalTheory.AdLat
