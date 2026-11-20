import Mathlib.Algebra.Module.PID
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

namespace GlobalTheory

open IsDiscreteValuationRing in

theorem dvr_fg_module_structure : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M], ∃ (n m : ℕ) (e : Fin m → ℕ),
    Nonempty (M ≃ₗ[O] (Fin n → O) × ((i : Fin m) → O ⧸ IsLocalRing.maximalIdeal O ^ e i)) := by
  intro O _ _ _ M _ _ _
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := M)
  have hid : ∀ i, (Submodule.span O {p i ^ e i} : Submodule O O) =
      (IsLocalRing.maximalIdeal O ^ e i : Ideal O) := by
    intro i
    rw [(irreducible_iff_uniformizer _).1 (hp i), Ideal.span_singleton_pow]
  classical
  let σ := Fintype.equivFin ι
  refine ⟨n, Fintype.card ι, fun j => e (σ.symm j), ⟨?_⟩⟩
  exact f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite O O (Fin n))
    (DirectSum.linearEquivFunOnFintype O ι (fun i => O ⧸ O ∙ p i ^ e i) ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => Submodule.quotEquivOfEq _ _ (hid i)) ≪≫ₗ
      (LinearEquiv.piCongrLeft O (fun i : ι => O ⧸ IsLocalRing.maximalIdeal O ^ e i) σ.symm).symm)

end GlobalTheory
