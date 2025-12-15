import VecLat.Basic
import VecLat.Maximal
import VecLat.Hom

open Maximal

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X]

variable (M : VectorOrderIdeal X) [IsMaximal M]
  (e : X) (epos : 0 < Quotient.mkQ M e)

def real_map : VecLatHom ℝ (X ⧸ M) where
  toFun := fun t => t • Quotient.mkQ M e
  map_add' := by
    intro t s
    exact add_smul t s _
  map_smul' := by
    intro t s
    simp
    exact mul_smul t s ((Quotient.mkQ M) e)
  map_sup' := by sorry
  map_inf' := by sorry

lemma real_map_injective : Function.Injective (real_map M e) := sorry
lemma real_map_surjective : Function.Surjective (real_map M e) := sorry
lemma real_map_bijective : Function.Bijective (real_map M e) := sorry

def character : VecLatHom X ℝ :=
  VecLatHom.comp (VecLatHom.symm (real_map M e) (real_map_bijective M e)) (Quotient.mkQ M)

theorem character_basis : (character M e) e = 1 := by sorry

theorem character_eval_M (x : X) (xmem : x ∈ M) : (character M e) x = 0 := by
  sorry
