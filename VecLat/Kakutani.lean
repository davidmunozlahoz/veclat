import VecLat.Character
import VecLat.CofK

open UnitalAMSpace Character

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X] {e : X} [IsUnitalAMSpace X e]

namespace Kakutani

def T (x : X) : C(Characters e, ℝ) where
  toFun := fun φ => (φ : X → ℝ) x
  continuous_toFun := sorry

theorem Kakutani : (IsVecLatHom T) ∧ (∀ x : X, ‖x‖=‖T x‖) ∧ (Dense
  (Set.range T)) ∧ (T e = 1) := sorry

end Kakutani
