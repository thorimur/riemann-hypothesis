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

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ}

abbrev Wd (e : Matrix (Fin N) (Fin N) k) : Submodule k (Fin N → k) := LinearMap.range e.mulVecLin

lemma mat_ext {b b' : Matrix (Fin N) (Fin N) k} (h : ∀ v, b *ᵥ v = b' *ᵥ v) : b = b' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma toMatrix'_mulVec' (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma W_fix {e : Matrix (Fin N) (Fin N) k} (hid : IsIdempotentElem e) {w : Fin N → k} (hw : w ∈ Wd e) :
    e *ᵥ w = w := by
  obtain ⟨v, rfl⟩ := hw
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hid.eq]

lemma W_stable {e a : Matrix (Fin N) (Fin N) k} (hc : a * e = e * a) {w : Fin N → k} (hw : w ∈ Wd e) :
    a *ᵥ w ∈ Wd e := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨a *ᵥ v, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc]⟩

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def rho (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) : A →ₐ[k] Module.End k (Wd e) where
  toFun a := (a.1.mulVecLin).restrict (fun w hw => W_stable (hA _ a.2 _ he) hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 * b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (b.1 *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec]
  map_zero' := by ext w; simp
  map_add' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 + b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (w : Fin N → k) + b.1 *ᵥ (w : Fin N → k)
    rw [Matrix.add_mulVec]
  commutes' r := by ext w; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

lemma rho_apply (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := rfl

abbrev Pe (e : Matrix (Fin N) (Fin N) k) : (Fin N → k) →ₗ[k] Wd e := LinearMap.rangeRestrict e.mulVecLin

lemma Pe_surj (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := LinearMap.surjective_rangeRestrict _

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
