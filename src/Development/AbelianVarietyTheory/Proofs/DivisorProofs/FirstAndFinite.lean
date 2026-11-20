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
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory.EtC

def firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    Subalgebra R (PiTensorProduct R (fun _ : Fin (k + 1) => A)) :=
  Algebra.adjoin R (Set.range (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0) ∪
    ⋃ i : Fin (k + 1), (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i) '' (F : Set A))

def firstIncl (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    A →ₐ[R] firstAndFinite R A k F :=
  (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

end GlobalTheory.EtC
