import VecLat.Basic
import VecLat.UnitalAMSpace

import Mathlib.Topology.ContinuousMap.Compact

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

namespace CofK

instance instLattice : Lattice C(K, ℝ) where
  le := fun f g => ∀ t : K, f t ≤ g t
  le_refl := by intro a t; exact le_refl (a t)
  le_trans := by intro _ _ _ h h' t; exact le_trans (h t) (h' t)
  le_antisymm := by intro f g h h'; ext t; exact le_antisymm (h t) (h' t)
  sup := fun f g => { toFun := (fun t => (f t) ⊔ (g t)) }
  le_sup_left := by
    intro f g t
    dsimp
    exact le_sup_left
  le_sup_right := by
    intro f g t
    dsimp
    exact le_sup_right
  sup_le := by
    intro f g h fh gh t
    dsimp
    exact sup_le (fh t) (gh t)
  inf := fun f g => { toFun := (fun t => (f t) ⊓ (g t)) }
  inf_le_left := by
    intro f g t
    dsimp
    exact inf_le_left
  inf_le_right := by
    intro f g t
    dsimp
    exact inf_le_right
  le_inf := by
    intro f g h fh gh t
    dsimp
    exact le_inf (fh t) (gh t)

instance instIsOrderedAddMonoid : IsOrderedAddMonoid C(K, ℝ) where
  add_le_add_left := by
    intro f g hfg h t
    simp [hfg t]

noncomputable instance instVectorLattice : VectorLattice C(K, ℝ) where
  smul_le_smul_of_nonneg_left := by
    intro f fpos g h hgh t
    exact smul_le_smul_of_nonneg_left (hgh t) fpos

/- Not needed, but for the future:

instance instArchimedean : Archimedean C(K, ℝ) := sorry
instance instIsUnitalAMSpace : IsUnitalAMSpace C(K, ℝ) 1 := sorry

and then show that the norm as an AMSpace coincides with the norm
already defined in C(K, ℝ). -/


end CofK
