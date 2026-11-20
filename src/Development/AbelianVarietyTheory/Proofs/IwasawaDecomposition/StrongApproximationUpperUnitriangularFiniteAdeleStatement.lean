import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdele

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles : PIW.ClassFinD.UnipApprox := by
  first | exact @GlobalTheory.UnipApproxGL.unipApprox | exact GlobalTheory.UnipApproxGL.unipApprox | (intros; apply GlobalTheory.UnipApproxGL.unipApprox <;> assumption)
