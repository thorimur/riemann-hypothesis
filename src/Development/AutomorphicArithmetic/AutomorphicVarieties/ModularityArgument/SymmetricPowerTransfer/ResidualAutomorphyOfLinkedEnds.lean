import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.Z.Sym.Top

open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl

theorem descUse_of_weak (h : Z.Desc.DescWeak) : Z.Desc.DescUse :=
  fun E _ _ _ hE p hp S hS h1 h2 n hn hn' π hr _ => h E hE p hp S hS h1 h2 n hn hn' π hr

end UpperTheory.V.Z.Sym.Top
