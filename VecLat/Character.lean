import VecLat.Hom
import VecLat.Maximal
import VecLat.UnitalAMSpace

import Mathlib.Topology.Algebra.Module.WeakDual

namespace UnitalAMSpace

namespace Character

noncomputable section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X] (e : X) [IsUnitalAMSpace X e]

theorem exist (x : X) (h : 1 < norm e x) :
  ∃ φ : VecLatHom X ℝ, (φ e = 1) ∧ (φ x  > 1) := by sorry

def Characters : Set (WeakDual ℝ X) := { φ | IsVecLatHom φ ∧ φ e = 1}

theorem attain_norm (x : X) :
    norm e x = sSup { φ x | φ ∈ Characters e } := by sorry

theorem closed : IsClosed (Characters e) := by sorry

theorem compact : IsCompact (Characters e) := by sorry
  /- Use:  WeakDual.isCompact_of_bounded_of_closed -/

instance instCompactSpace : CompactSpace (Characters e) := by
  exact isCompact_iff_compactSpace.mp (compact e)

/- TO DO:
- In another file (Kakutani.lean), define the evaluation map T x:
Characters e → \R and show that it is continuous.
- Show that the map T: X → C(Characters e) is: Te=1, lattice
homomorphism, injective and has dense range.
-/

end

end Character

end UnitalAMSpace
