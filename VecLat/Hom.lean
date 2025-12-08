import VecLat.Basic
import VecLat.VectorOrderIdeal

variable (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

structure VecLatHom extends X →ₗ[ℝ] Y, LatticeHom X Y

namespace VecLatHom

instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective' f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)

instance instLatticeHomClass : LatticeHomClass (VecLatHom X Y) X Y where
  map_inf := by
    intro f a b
    exact f.toLatticeHom.map_inf' a b
  map_sup := by
    intro f a b
    exact f.toLatticeHom.map_sup' a b

instance instLinearMapClass : LinearMapClass (VecLatHom X Y) ℝ X Y where
  map_add := by
    intro f a b
    exact f.toLinearMap.map_add a b
  map_smulₛₗ := by
    intro f c x
    simp
    exact f.toLinearMap.map_smul c x

@[simp]
theorem toFun_eq_coe {f : VecLatHom X Y} : f.toFun = (f : X → Y) := rfl

lemma map_abs (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by simp

lemma monotone (f : VecLatHom X Y) : Monotone f := by
  intro x y hxy
  have : x ⊔ y = y := by simp [hxy]
  rw [← sup_eq_right, ← map_sup f x y, this]

def of_abs (f : X →ₗ[ℝ] Y) (abs : ∀ x : X, f |x| = |f x|) : VecLatHom X Y :=
  {f with
      map_sup' := by
        intro x y
        simp
        rw [sup_eq_half_smul_add_add_abs_sub ℝ,sup_eq_half_smul_add_add_abs_sub ℝ]
        rw [f.map_smul ⅟2 (x + y + |y-x|)]
        congr
        rw [f.map_add, f.map_add]
        congr
        rw [abs (y-x)]
        congr
        exact f.map_sub y x
      map_inf' := by
        intro x y
        simp
        rw [inf_eq_half_smul_add_sub_abs_sub ℝ,inf_eq_half_smul_add_sub_abs_sub ℝ]
        rw [f.map_smul ⅟2 (x + y - |y-x|)]
        congr
        rw [f.map_sub, f.map_add]
        congr
        rw [abs (y-x)]
        congr
        exact f.map_sub y x
    }

def ker (f : VecLatHom X Y) : VectorOrderIdeal X :=
  {LinearMap.ker f with
    supClosed' := by
      intro x xmem y ymem
      simp_all
    infClosed' := by
      intro x xmem y ymem
      simp_all
    solid := by
      intro x y hxy ymem
      simp
      simp at ymem
      rw [← abs_eq_zero_iff_zero]
      apply le_antisymm
      · calc
          |f x| = f |x| := by simp
              _ ≤ f |y| := by apply (f.monotone X Y) hxy
              _ = |f y| := by simp
              _ = 0     := by simp [ymem]
      · exact abs_nonneg _
  }

end VecLatHom
