import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.Topology.Sheaves.Presheaf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem pullbackCone_ker_fst_inf_ker_snd {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ⊓
      RingHom.ker (CommRingCat.pullbackCone f g).snd.hom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker] at hx
  rw [Ideal.mem_bot]
  exact Subtype.ext (Prod.ext hx.1 hx.2)

theorem pow_le_ker_of_le_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (k : ℕ) (hIJ : I ≤ Ideal.comap φ J) (hJ : J ^ k = 0) :
    I ^ k ≤ RingHom.ker φ :=
  calc I ^ k ≤ (Ideal.comap φ J) ^ k := Ideal.pow_right_mono hIJ k
    _ ≤ Ideal.comap φ (J ^ k) := Ideal.le_comap_pow φ k
    _ = RingHom.ker φ := by rw [hJ, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

theorem pullbackCone_fst_snd_ring_nilpotent {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom →
    IsNilpotent (RingHom.ker g.hom) →
    (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧
      (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧
      (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧
        IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  rintro hf ⟨n, hn⟩ hg ⟨m, hm⟩
  have hbot := pullbackCone_ker_fst_inf_ker_snd f g
  have hcomm : ∀ x : (CommRingCat.pullbackCone f g).pt,
      f.hom ((CommRingCat.pullbackCone f g).fst.hom x) =
        g.hom ((CommRingCat.pullbackCone f g).snd.hom x) := fun x => x.2
  have k1 : RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm, hx, map_zero]
  have k2 : RingHom.ker (CommRingCat.pullbackCone f g).snd.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm, hx, map_zero]
  have k3 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hx
  have k4 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm]
    simpa using hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a
    obtain ⟨b, hb⟩ := hg (f.hom a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · refine ⟨m + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf inf_le_right ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ m k1 hm)))
  · intro b
    obtain ⟨a, ha⟩ := hf (g.hom b)
    exact ⟨⟨(a, b), ha⟩, rfl⟩
  · refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k2 hn)) inf_le_right)
  · intro c
    obtain ⟨a, ha⟩ := hf c
    obtain ⟨b, hb⟩ := hg c
    exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩
  · refine ⟨n + m, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_add]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k3 hn))
        ((inf_le_right).trans (pow_le_ker_of_le_comap _ _ _ m k4 hm)))

end GlobalTheory
