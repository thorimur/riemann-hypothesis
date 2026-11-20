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
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_torsionFree_of_card_quotient_pow (l : ℕ) [Fact l.Prime] (C : Type)
    [AddCommGroup C] [Module ℤ_[l] C] [Module.Finite ℤ_[l] C]
    (h : ∀ r : ℕ, 0 < r →
      Nat.card (C ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))) = l ^ r) :
    ∀ (r : ℕ) (c : C), (l : ℤ_[l]) ^ r • c = 0 → c = 0 := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let N : ℕ → AddSubgroup C := fun r =>
    (LinearMap.range (LinearMap.lsmul ℤ_[l] C ((l : ℤ_[l]) ^ r))).toAddSubgroup
  have hmem : ∀ r (x : C), x ∈ N r ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x := fun r x => Iff.rfl
  have hidx : ∀ r, 0 < r → (N r).index = l ^ r := fun r hr => h r hr
  let f : C →+ C := (LinearMap.lsmul ℤ_[l] C (l : ℤ_[l])).toAddMonoidHom
  have hf : ∀ x, f x = (l : ℤ_[l]) • x := fun x => rfl
  have hrange : f.range = N 1 := by
    ext x
    rw [hmem]
    simp only [AddMonoidHom.mem_range, hf, pow_one]
  have key : ∀ c : C, (l : ℤ_[l]) • c = 0 → ∀ k, 0 < k → c ∈ N k := by
    intro c hc k hk
    have h1 : N (k + 1) ≤ N 1 := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨(l : ℤ_[l]) ^ k • y, by rw [smul_smul, ← pow_add, add_comm]⟩
    have h2 := AddSubgroup.relIndex_mul_index h1
    rw [hidx 1 one_pos, hidx (k + 1) k.succ_pos, pow_one, pow_succ] at h2
    have h3 : ((N (k + 1)).comap f).index = l ^ k := by
      rw [AddSubgroup.index_comap, hrange]
      exact Nat.eq_of_mul_eq_mul_right hl h2
    have h4 : N k ≤ (N (k + 1)).comap f := by
      intro x hx
      obtain ⟨y, rfl⟩ := (hmem _ _).1 hx
      exact (hmem _ _).2 ⟨y, by rw [hf, smul_smul, pow_succ']⟩
    have h5 := AddSubgroup.relIndex_mul_index h4
    rw [h3, hidx k hk] at h5
    have h6 : (N k).relIndex ((N (k + 1)).comap f) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hl k) (by rw [h5, one_mul])
    apply AddSubgroup.relIndex_eq_one.1 h6
    show f c ∈ N (k + 1)
    rw [hf, hc]
    exact zero_mem _
  have one : ∀ c : C, (l : ℤ_[l]) • c = 0 → c = 0 := by
    intro c hc
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C)
      (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [← Submodule.mem_bot ℤ_[l], ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨y, hy⟩ := (hmem _ _).1 (key c hc (i + 1) i.succ_pos)
    rw [← hy, pow_succ, mul_smul]
    refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ i) Submodule.mem_top
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  intro r
  induction r with
  | zero => intro c hc; simpa using hc
  | succ r ih =>
    intro c hc
    rw [pow_succ, mul_smul] at hc
    exact one c (ih _ hc)

end GlobalTheory
