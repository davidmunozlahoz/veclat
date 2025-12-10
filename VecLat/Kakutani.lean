import VecLat.Character
import VecLat.CofK

open UnitalAMSpace Character

variable (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X] (e : X) [IsUnitalAMSpace X e]

def KT (x : X) : C(Characters e, ℝ) where
  toFun := fun φ => (φ : X → ℝ) x
  continuous_toFun := sorry

theorem Kakutani : (IsVecLatHom (KT X e)) ∧ (∀ x : X, ‖x‖=‖KT X e x‖) ∧ (Dense
  (Set.range (KT X e))) ∧ (KT X e e = 1) := sorry
