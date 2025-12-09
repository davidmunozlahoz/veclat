import VecLat.Basic

variable (X : Type*) (Y : Type*) [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

structure VecLatHom extends X →ₗ[ℝ] Y, LatticeHom X Y

variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]

structure IsVecLatHom (f : X → Y) extends IsLinearMap ℝ f where
  map_sup' : ∀ x y : X, f (x ⊔ y) = (f x) ⊔ (f y)
  map_inf' : ∀ x y : X, f (x ⊓ y) = (f x) ⊓ (f y)

namespace VecLatHom

instance instFunLike : FunLike (VecLatHom X Y) X Y where
  coe f := f.toFun
  coe_injective' f g h := by
    dsimp at h
    cases f
    cases g
    congr
    exact LinearMap.ext_iff.mpr (congrFun h)

theorem isVecLatHom (f : VecLatHom X Y) : IsVecLatHom f where
  map_add := f.toLinearMap.map_add
  map_smul := f.toLinearMap.map_smul
  map_sup' := f.toLatticeHom.map_sup'
  map_inf' := f.toLatticeHom.map_inf'

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

end VecLatHom
