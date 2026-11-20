import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
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
import Mathlib.Order.CompletePartialOrder
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem idealSheafData_wellFoundedGT :
    ∀ {X : Scheme.{0}} [IsNoetherian X], WellFoundedGT X.IdealSheafData := by
  intro X _
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U.1 : X.Opens) : Set X)) (fun U => U.1.isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, (U.1 : X.Opens)) := by
        rw [iSup_affineOpens_eq_top X]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  have hcov : ⨆ i : t, ((i.1 : X.affineOpens).1 : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨U, hUt, hxU⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  have hnoeth : ∀ i : t, WellFoundedGT (Ideal Γ(X, (i.1 : X.affineOpens).1)) := fun i => by
    haveI : IsNoetherianRing Γ(X, (i.1 : X.affineOpens).1) :=
      IsLocallyNoetherian.component_noetherian i.1
    infer_instance
  let φ : X.IdealSheafData → (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) :=
    fun I i => I.ideal i.1
  have hφ : StrictMono φ := by
    refine Monotone.strictMono_of_injective (fun I J h i => h i.1) ?_
    intro I J h
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : t => i.1) hcov
      (fun i => congrFun h i)
  have h1 : WellFoundedLT (∀ i : t, (Ideal Γ(X, (i.1 : X.affineOpens).1))ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i : t, Ideal Γ(X, (i.1 : X.affineOpens).1)) := ⟨h1.wf⟩
  exact hφ.wellFoundedGT

end GlobalTheory.CompanionTheory.GE
