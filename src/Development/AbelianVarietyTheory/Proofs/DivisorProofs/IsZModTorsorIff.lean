import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.TorsorColim

def bcAct (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) : G →* (S ⊗[R] A ≃ₐ[S] S ⊗[R] A) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]

@[simp]
theorem bcAct_tmul (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) (g : G) (s : S) (a : A) :
    bcAct S act g (s ⊗ₜ[R] a) = s ⊗ₜ[R] act g a := rfl

def prodMapOf (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    D ⊗[B] D →ₐ[B] (Multiplicative (ZMod q) → D) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))

@[simp]
theorem prodMapOf_tmul (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (x y : D) (g : Multiplicative (ZMod q)) :
    prodMapOf B D q act (x ⊗ₜ[B] y) g = x * act g y := by
  simp [prodMapOf]

theorem eventually_and {J : Type} [Category J] [IsFiltered J] {j : J}
    (P Q : ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f))
    (hQ : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), Q k (f₀ ≫ f)) :
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f) ∧ Q k (f₀ ≫ f) := by
  obtain ⟨k₁, f₁, h₁⟩ := hP
  obtain ⟨k₂, f₂, h₂⟩ := hQ
  let a := IsFiltered.leftToMax k₁ k₂
  let b := IsFiltered.rightToMax k₁ k₂
  let e := IsFiltered.coeqHom (f₁ ≫ a) (f₂ ≫ b)
  have he : (f₁ ≫ a) ≫ e = (f₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (f₁ ≫ a) (f₂ ≫ b), (f₁ ≫ a) ≫ e, fun k f => ⟨?_, ?_⟩⟩
  · have := h₁ k (a ≫ e ≫ f)
    simpa only [Category.assoc] using this
  · have := h₂ k (b ≫ e ≫ f)
    rw [he]
    simpa only [Category.assoc] using this

end GlobalTheory.TorsorColim
