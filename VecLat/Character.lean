import VecLat.Hom
import VecLat.Maximal
import VecLat.UnitalAMSpace

namespace UnitalAMSpace

namespace Character

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] (e : X) [UnitalAMSpace X e]

theorem exist (x : X) (h : 1 < norm e x) :
  ∃ φ : VecLatHom X ℝ, (φ e = 1) ∧ (φ x  > 1) := by sorry

def Characters : Set (StrongDual ℝ X) := { φ | IsVecLatHom φ ∧ φ e = 1}

theorem attain_norm (x : X) :
    norm e x = sSup { φ x | φ ∈ Characters e } := by sorry

/- TO DO:
- Equip Characters e with the w*-topology inherited from StrongDual ℝ
X.
- Show that it is closed in this topology.
- Show that it is contained in the unit ball.
- Use Banach--Alaoglu to show that it is compact.
- In another file (Kakutani.lean), define the evaluation map T x:
Characters e → \R and show that it is continuous.
- Show that C(K) is an instance of a VectorLattice for every K.
- Show that the map T: X → C(Characters e) is: Te=1, lattice
homomorphism, injective and has dense range.
-/

end Character

end UnitalAMSpace
