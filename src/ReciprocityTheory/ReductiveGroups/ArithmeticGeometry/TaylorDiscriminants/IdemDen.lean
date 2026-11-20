import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.DedekindDomain.Different
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

open NumberField TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB

def trDual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    Module.Basis ι ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b

def idemOf {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [Algebra ℚ C] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, trDual b i ⊗ₜ[ℚ] τ (b i)

def evAt {E : Type} [Field E] {C : Type} [Field C] [Algebra ℚ E] [Algebra ℚ C] (σ : E →+* C) :
    E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap (σ.toRatAlgHom) (AlgHom.id ℚ C)

open Classical in

def IdemEvalSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ σ : E →+* C),
    evAt σ (idemOf b τ) = if σ = τ then 1 else 0

def DualDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E),
    (∀ i, IsIntegral ℤ (b i)) →
    (∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual b i)

end ReciprocityTheory.ChartRestriction.G.TB
