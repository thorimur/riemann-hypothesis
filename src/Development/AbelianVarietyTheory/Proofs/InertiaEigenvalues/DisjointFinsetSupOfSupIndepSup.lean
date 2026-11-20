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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory

theorem disjoint_finset_sup_of_supIndep_sup :
    ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V),
      F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) →
        Disjoint (F.sup G) (F.sup B) := by
  intro R V ι _ _ _ F G B hind hdis
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s.SupIndep (fun i => G i ⊔ B i) := hind.subset (Finset.subset_insert _ _)
    have ih' := ih hs (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    have hA : Disjoint (G a ⊔ B a) (s.sup fun i => G i ⊔ B i) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    have hGs : s.sup G ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_left)
    have hBs : s.sup B ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_right)
    rw [Finset.sup_insert, Finset.sup_insert, Submodule.disjoint_def]
    intro x hxG hxB
    obtain ⟨g, hg, g', hg', rfl⟩ := Submodule.mem_sup.mp hxG
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp hxB
    have h1 : g - b ∈ G a ⊔ B a := Submodule.sub_mem _ (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hb)
    have h2 : g - b ∈ s.sup (fun i => G i ⊔ B i) := by
      have : g - b = b' - g' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b' b, hbb]
      rw [this]
      exact Submodule.sub_mem _ (hBs hb') (hGs hg')
    have h3 : g - b = 0 := (Submodule.disjoint_def.mp hA) _ h1 h2
    have hgb : g = b := sub_eq_zero.mp h3
    have hg0 : g = 0 := (Submodule.disjoint_def.mp (hdis a (Finset.mem_insert_self a s))) g hg (hgb ▸ hb)
    have hg'b' : g' = b' := by
      subst hgb
      exact add_left_cancel hbb.symm
    have hg'0 : g' = 0 := (Submodule.disjoint_def.mp ih') g' hg' (hg'b' ▸ hb')
    rw [hg0, hg'0, add_zero]

end GlobalTheory
