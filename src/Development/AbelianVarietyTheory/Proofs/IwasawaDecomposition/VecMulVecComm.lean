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

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel

variable (n : ℕ)

abbrev Ext : Type := ExteriorAlgebra ℂ (Fin n → ℂ)

abbrev Big : Type := Ext n ⊗[ℂ] Ext n

def vec (a : Fin n) : Ext n := ExteriorAlgebra.ι ℂ (Pi.single a 1 : Fin n → ℂ)

def gen (x : Fin n × Fin n) : Big n := vec n x.1 ⊗ₜ vec n x.2

theorem vec_mul_vec_comm (a b : Fin n) : vec n a * vec n b = -(vec n b * vec n a) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem gen_comm : ∀ u ∈ Set.range (gen n), ∀ v ∈ Set.range (gen n), u * v = v * u := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [gen, Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n x.1, vec_mul_vec_comm n x.2,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

abbrev EvenPart : Subalgebra ℂ (Big n) := Algebra.adjoin ℂ (Set.range (gen n))

open scoped IsMulCommutative in
instance : CommRing (EvenPart n) :=
  have := Algebra.isMulCommutative_adjoin ℂ (gen_comm n)
  inferInstance

def toEven : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] EvenPart n :=
  aeval fun x => ⟨gen n x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

open Classical in

def topForm (i : ℕ) : (Fin n → ℂ) [⋀^Fin i]→ₗ[ℂ] ℂ :=
  if h : i = n then (Pi.basisFun ℂ (Fin n)).det.domDomCongr (finCongr h.symm) else 0

def topExt : Ext n →ₗ[ℂ] ℂ := ExteriorAlgebra.liftAlternating (topForm n)

def topBig : Big n →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₂ (topExt n) ∘ₗ topExt n)

theorem topBig_tmul (x y : Ext n) : topBig n (x ⊗ₜ y) = topExt n x * topExt n y := rfl

variable {n} {p q : ℕ}

def blockPoly (e : Fin p × Fin q → Fin n) : Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b, X (e (i, b), e (j, b))

def blockPolyBar (e : Fin p × Fin q → Fin n) : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun b b' => ∑ i, X (e (i, b), e (i, b'))

end GlobalTheory.GrassModel
