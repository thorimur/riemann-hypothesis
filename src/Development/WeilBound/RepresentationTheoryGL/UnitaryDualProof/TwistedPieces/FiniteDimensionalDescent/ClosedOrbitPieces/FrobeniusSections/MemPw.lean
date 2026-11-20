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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module

def Tw (k : Type*) (_p _c : ℕ) : Type _ := k

variable {k : Type*} [Field k]

instance (p c : ℕ) : Field (Tw k p c) := inferInstanceAs (Field k)

instance (p c : ℕ) [Fact p.Prime] [CharP k p] : Algebra k (Tw k p c) :=
  RingHom.toAlgebra (show k →+* Tw k p c from iterateFrobenius k p c)

def Pw (k B : Type*) [Field k] [CommRing B] [Algebra k B] (q : ℕ) : Subalgebra k B :=
  Algebra.adjoin k (Set.range fun b : B => b ^ q)

theorem mem_Pw {B : Type*} [CommRing B] [Algebra k B] (p c : ℕ) [Fact p.Prime] [CharP k p]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) {b : B} :
    b ∈ Pw k B (p ^ c) ↔ ∃ w : B, w ^ (p ^ c) = b := by
  unfold Pw
  constructor
  · intro hb
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact ⟨b, Subsingleton.elim _ _⟩
    have : CharP B p := charP_of_injective_algebraMap' k p
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    | algebraMap r => exact hroot r
    | add x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ + w₂, add_pow_char_pow w₁ w₂ p c⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ * w₂, mul_pow w₁ w₂ _⟩
  · rintro ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w, rfl⟩

theorem fc {B : Type*} [CommRing B] [Algebra k B] [FiniteDimensional k B] [IsReduced B]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) :
    finrank k B = finrank k (Tw k p c) * finrank k (Pw k B (p ^ c)) := by
  classical
  letI iT : Module (Tw k p c) (Pw k B (p ^ c)) := inferInstanceAs (Module k (Pw k B (p ^ c)))
  have hadd : ∀ x y : B, (x + y) ^ (p ^ c) = x ^ (p ^ c) + y ^ (p ^ c) := by
    intro x y
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact Subsingleton.elim _ _
    · haveI := charP_of_injective_algebraMap (algebraMap k B).injective p
      exact add_pow_char_pow x y p c
  have hmem : ∀ x : B, x ^ (p ^ c) ∈ Pw k B (p ^ c) := fun x =>
    Algebra.subset_adjoin ⟨x, rfl⟩
  let f : B →ₗ[k] RestrictScalars k (Tw k p c) (Pw k B (p ^ c)) :=
    { toFun := fun x => (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c))
      map_add' := fun x y => by
        apply Subtype.ext
        exact hadd x y
      map_smul' := fun a x => by
        apply Subtype.ext
        show (a • x) ^ (p ^ c) = ((algebraMap k (Tw k p c) a) • (⟨x ^ (p ^ c), hmem x⟩ : Pw k B (p ^ c)) : Pw k B (p ^ c)).1
        rw [smul_pow]
        rfl }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h0 : x ^ (p ^ c) = 0 := congrArg (fun z : Pw k B (p ^ c) => (z : B)) hx
    exact IsReduced.eq_zero x ⟨_, h0⟩
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).1 (show (Pw k B (p ^ c)) from y).2
    exact ⟨w, Subtype.ext hw⟩
  letI : Module (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    RestrictScalars.moduleOrig k (Tw k p c) (Pw k B (p ^ c))
  haveI : Module.Free (Tw k p c) (RestrictScalars k (Tw k p c) (Pw k B (p ^ c))) :=
    show Module.Free k (Pw k B (p ^ c)) from inferInstance
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [e.finrank_eq, ← Module.finrank_mul_finrank k (Tw k p c)
    (RestrictScalars k (Tw k p c) (Pw k B (p ^ c)))]
  rfl

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
