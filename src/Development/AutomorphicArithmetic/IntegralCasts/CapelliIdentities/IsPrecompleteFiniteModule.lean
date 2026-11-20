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
import Mathlib.RingTheory.AdicCompletion.Exactness
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

private theorem UpperTheory.Reformulated.B.Qk17.pi_precomplete {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, IsPrecomplete I (N i)] : IsPrecomplete I (∀ i, N i) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose r hr using fun j : ι =>
    AdicCompletion.of_surjective I (N j) (AdicCompletion.pi I N y j)
  refine ⟨r, (AdicCompletion.piEquivOfFintype I N).injective ?_⟩
  rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.piEquivOfFintype_apply]
  funext j
  rw [← hr j]
  exact AdicCompletion.map_of I (LinearMap.proj (R := R) (φ := N) j) r

theorem UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type u_2)
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] [Module.Finite R M], IsPrecomplete I M := by
  intro R _ I _ M _ _ _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have := UpperTheory.Reformulated.B.Qk17.pi_precomplete I (fun _ : Fin n => R)
  rw [← AdicCompletion.of_surjective_iff]
  intro x
  obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective I hf x
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I (Fin n → R) y
  exact ⟨f r, (AdicCompletion.map_of I f r).symm⟩
