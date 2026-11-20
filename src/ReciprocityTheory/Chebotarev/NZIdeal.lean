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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Basic
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

open NumberField

namespace ReciprocityTheory.Cheb

noncomputable section

abbrev NZIdeal (E : Type) [Field E] [NumberField E] : Type := {a : Ideal (𝓞 E) // a ≠ ⊥}

abbrev Prm (E : Type) [Field E] [NumberField E] : Type := IsDedekindDomain.HeightOneSpectrum (𝓞 E)

def Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : ℕ := Ideal.absNorm q.asIdeal

def Lser (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' a : NZIdeal E, χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

def Psum (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))

def abelian₂ (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, -Complex.log (1 - χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))

def PE (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-s)

def Pcl (E : Type) [Field E] [NumberField E] (l : ℕ) (a : ZMod l) (s : ℝ) : ℝ :=
  ∑' q : Prm E, if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0

end

end ReciprocityTheory.Cheb
