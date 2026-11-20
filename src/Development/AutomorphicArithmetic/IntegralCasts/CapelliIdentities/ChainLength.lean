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

theorem UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain :
    ∀ {O X : Type} [inst : CommRing O] [inst_1 : AddCommGroup X]
    [inst_2 : _root_.Module O X] {A B C : Submodule O X},
    A ≤ B →
      B ≤ C →
        Module.length O (↥C ⧸ Submodule.comap C.subtype A) =
          Module.length O (↥B ⧸ Submodule.comap B.subtype A) + Module.length O (↥C ⧸ Submodule.comap C.subtype B) := by
  intro O X _ _ _ A B C hAB hBC
  let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype A) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBC) (fun x hx => hx)
  let g : (↥C ⧸ Submodule.comap C.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype B) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hAB hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      intro h
      have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype A)
          (Submodule.inclusion hBC x) = 0 := h
      rw [Submodule.Quotient.mk_eq_zero] at h' ⊢
      exact h'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype B) x = 0 := h
        rw [Submodule.Quotient.mk_eq_zero] at h'
        exact ⟨Submodule.Quotient.mk ⟨x.1, h'⟩, rfl⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        induction z using Submodule.Quotient.induction_on with
        | H w =>
          have : Submodule.Quotient.mk (p := Submodule.comap C.subtype B)
              (Submodule.inclusion hBC w) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).2 w.2
          exact this
