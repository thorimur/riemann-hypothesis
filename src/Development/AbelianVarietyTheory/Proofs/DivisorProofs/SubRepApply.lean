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
import Mathlib.RepresentationTheory.Basic
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

namespace GlobalTheory.CharFlag

variable {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]

def Stab (π : Representation k Γ V) (S : Submodule k V) : Prop := ∀ g, ∀ x ∈ S, π g x ∈ S

def subRep (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) : Representation k Γ S where
  toFun g := (π g).restrict (hS g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem subRep_apply (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) (g : Γ) (x : S) :
    ((subRep π S hS g x : S) : V) = π g x := rfl

def quotRep (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) : Representation k Γ (V ⧸ S) where
  toFun g := S.mapQ S (π g) (hS g)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp
  map_mul' g h := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp

def HasCharFlag (π : Representation k Γ V) {t : ℕ} (ψ : Fin t → Γ →* kˣ) : Prop :=
  ∃ (R : ℕ) (W : Fin (R + 1) → Submodule k V) (rs : Fin t → Fin R), W 0 = ⊥ ∧ W (Fin.last R) = ⊤ ∧
    Monotone W ∧ (∀ g j x, x ∈ W j → π g x ∈ W j) ∧ Function.Injective rs ∧
    ∀ s, ∃ x ∈ W (rs s).succ, x ∉ W (rs s).castSucc ∧
      W (rs s).succ = W (rs s).castSucc ⊔ Submodule.span k {x} ∧
      ∀ g, π g x - ((ψ s g : kˣ) : k) • x ∈ W (rs s).castSucc

end GlobalTheory.CharFlag
