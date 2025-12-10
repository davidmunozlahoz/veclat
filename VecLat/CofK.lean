import VecLat.Basic
import VecLat.UnitalAMSpace

import Mathlib.Topology.ContinuousMap.Compact

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

namespace CofK

instance instLattice : Lattice C(K, ℝ) := sorry

instance instIsOrderedAddMonoid : IsOrderedAddMonoid C(K, ℝ) := sorry

instance instVectorLattice : VectorLattice C(K, ℝ) := sorry

/- Not needed, but for the future:

instance instArchimedean : Archimedean C(K, ℝ) := sorry
instance instIsUnitalAMSpace : IsUnitalAMSpace C(K, ℝ) 1 := sorry

and then show that the norm as an AMSpace coincides with the norm
already defined in C(K, ℝ). -/


end CofK
