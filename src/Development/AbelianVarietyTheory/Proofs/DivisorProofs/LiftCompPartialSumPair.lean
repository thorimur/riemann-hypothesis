import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.MumFam
variable {R : Type} [CommRing R] [IsDomain R]

section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G)

theorem padd_eq_mul' (x y : T ⟶ G) : padd G x y = x * y := rfl
theorem pzero_eq_one' : pzero G T = 1 := rfl

theorem psum_pair_01 : psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_0 : psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_1 : psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_e : psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero_eq_one']
end

end GlobalTheory.MumFam
