import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem q_of_unit {N : ℕ} {A : Type} [CommRing A] (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∃ i, IsUnit (v i)) :
    IsUnit (v (Fin.last N)) ∨ Ideal.span (v '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨i, hi⟩ := h
  by_cases hl : i = Fin.last N
  · left
    rw [← hl]
    exact hi
  · right
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hl
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩) hi

theorem UpperTheory.two_open_cover_of_map_incl :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc), Cover2 R (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E (incl (Q1 N)) (incl (Q2 N)) (fun A x y h => Subtype.ext h) (fun A x y h => Subtype.ext h)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um (N + 1) Γ(T, ⊤) from x).1 (show Um (N + 1) Γ(T, ⊤) from x).2
  refine ⟨S, hS, fun V g hg => ?_⟩
  let w : (XC (N + 1)).D.obj Γ(V, ⊤) := (XC (N + 1)).D.map g.appTop x
  rcases q_of_unit (fun i => g.appTop.hom ((show Um (N + 1) Γ(T, ⊤) from x).1 i))
      (show Um (N + 1) Γ(V, ⊤) from (XC (N + 1)).D.map g.appTop x).2 (hP V g hg) with h | h
  · have h' : (Q1 N).P Γ(V, ⊤) w := h
    exact Or.inl ⟨⟨w, h'⟩, rfl⟩
  · have h' : (Q2 N).P Γ(V, ⊤) w := h
    exact Or.inr ⟨⟨w, h'⟩, rfl⟩
