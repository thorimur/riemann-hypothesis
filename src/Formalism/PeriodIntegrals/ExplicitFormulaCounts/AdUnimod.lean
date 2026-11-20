import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdIndexEq

theorem adUnimod_closed : PI.AdUnimod :=
  PI.WAU.adUnimod_of PI.WAU.kg_subgroup PI.WAU.maximal_compact_isCompact PI.WAU.compact_countable PI.adelic_index_eq
