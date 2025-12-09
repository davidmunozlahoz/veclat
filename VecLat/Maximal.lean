import VecLat.Quotient
import VecLat.Lattice

variable {X : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

namespace VectorOrderIdeal

class IsMaximal (I : VectorOrderIdeal X) : Prop where
  out : IsCoatom I

variable (I : VectorOrderIdeal X) [IsMaximal I]

instance : LinearOrder (X ⧸ I) := by sorry

theorem exists_le_maximal (hI : I ≠ ⊤) :
    ∃ (M : VectorOrderIdeal X), M.IsMaximal ∧ I ≤ M := by sorry

namespace Maximal

theorem trivial_ideals (J : VectorOrderIdeal (X ⧸ I)) : (J = ⊥) ∨ (J = ⊤) := by sorry

theorem arch : Archimedean (X ⧸ I) := by sorry

theorem one_dim (x y : X) (h : I.mkQ y ≠ 0) : ∃! t : ℝ,
  I.mkQ x = t • I.mkQ y := by sorry

end Maximal

end VectorOrderIdeal
