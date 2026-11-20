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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory

open WittVector

theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (ι : Type*) [Finite ι] : IsPrecomplete I (ι → R) := by
  classical
  cases nonempty_fintype ι
  have coord : ∀ (J : Ideal R) (x : ι → R),
      x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R R) := by
    intro J x
    constructor
    · intro hx i
      have h1 := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (ι → R) →ₗ[R] R)) hx
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono le_rfl le_top h1
    · intro hx
      have hsum : x = ∑ i, (x i) • (Pi.single i (1 : R) : ι → R) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : x i ∈ J := by simpa using hx i
      exact Submodule.smul_mem_smul hi Submodule.mem_top
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec inferInstance (f := fun n => f n i) ?_
    intro m n hmn
    have := hf hmn
    rw [SModEq.sub_mem, coord] at this
    rw [SModEq.sub_mem]
    exact this i
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, coord]
  intro i
  have := hL i n
  rwa [SModEq.sub_mem] at this

section

variable {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [PerfectRing k p]
  [Field k'] [CharP k' p] [PerfectRing k' p]

end

end GlobalTheory
