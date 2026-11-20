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

noncomputable def UpperTheory.Reformulated.B.DaGva8.prodE :
    {G₁ G₂ : Type} →
      [inst : Group G₁] →
        [inst_1 : TopologicalSpace G₁] →
          [inst_2 : Group G₂] →
            [inst_3 : TopologicalSpace G₂] → (T₁ : Subgroup G₁) → (T₂ : Subgroup G₂) → ↥T₁ × ↥T₂ ≃ₜ* ↥(T₁.prod T₂) :=
  fun {_ _} _ _ _ _ T₁ T₂ =>
    { toFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
      invFun := fun y => (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      continuous_invFun :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }
