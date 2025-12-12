import VecLat.Basic
import VecLat.Hom

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]

structure VectorSublattice (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X] : Type u extends
  Submodule ℝ X,
  Sublattice X

namespace VectorSublattice

instance instSetLike : SetLike (VectorSublattice X) X where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s; cases t; congr; exact SetLike.coe_injective' h

@[ext]
theorem ext {s t : VectorSublattice X} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  SetLike.ext h

instance instAddCommGroup (Y : VectorSublattice X) : AddCommGroup Y :=
  Y.toAddSubgroup.toAddCommGroup

instance instLattice (Y : VectorSublattice X) : Lattice Y :=
  Y.instLatticeCoe

instance instIsOrderedAddMonoid (Y : VectorSublattice X) : IsOrderedAddMonoid Y where
  add_le_add_left := by
    intro x y hxy c
    exact @add_le_add_left X _ _ _ x y hxy c

instance instVectorLattice (Y : VectorSublattice X) : VectorLattice Y :=
  {
  toModule := Y.module
  smul_le_smul_of_nonneg_left := by
    intros a ha b b' hbs
    have : (b:X) ≤ (b':X) := hbs
    calc
      a • b = a • (b:X) := by simp
          _ ≤ a • (b':X) := by exact smul_le_smul_of_nonneg_left this ha
          _ = a • b' := by simp
  }

lemma abs_mem {Y : VectorSublattice X} {x : X} (h : x ∈ Y) : |x| ∈ Y := by
  exact Y.sup_mem h (Y.neg_mem h)

def ofSubmoduleAbs (s : Submodule ℝ X) (h : ∀ x ∈ s, |x| ∈ s) :
    VectorSublattice X := {
  carrier := s
  zero_mem' := s.zero_mem'
  add_mem' := s.add_mem'
  smul_mem' := s.smul_mem'
  supClosed' := by
    intro x hx y hy
    rw [sup_eq_half_smul_add_add_abs_sub ℝ]
    apply s.smul_mem
    apply s.add_mem
    · apply s.add_mem
      · exact hx
      · exact hy
    · apply h; exact s.sub_mem hy hx
  infClosed' := by
    intro x hx y hy
    rw [inf_eq_half_smul_add_sub_abs_sub ℝ]
    apply s.smul_mem
    apply s.sub_mem
    · apply s.add_mem
      · exact hx
      · exact hy
    · apply h; exact s.sub_mem hy hx
  }

variable {Y : Type u} [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]

def comap (f : VecLatHom X Y) (Z : VectorSublattice Y) :
    VectorSublattice X :=
  {Submodule.comap f Z.toSubmodule with
    supClosed' := by
      intro a amem b bmem
      simp at amem bmem
      simp
      exact Z.supClosed amem bmem
    infClosed' := by
      intro a amem b bmem
      simp at amem bmem
      simp
      exact Z.infClosed amem bmem
  }

end VectorSublattice

structure VectorOrderIdeal (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X] : Type u
  extends VectorSublattice X where
  solid : ∀ {x y : X}, |x| ≤ |y| → y ∈ carrier → x ∈ carrier

namespace VectorOrderIdeal

instance instSetLike : SetLike (VectorOrderIdeal X) X where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s; cases t; congr; exact SetLike.coe_injective' h

@[ext]
theorem ext {s t : VectorOrderIdeal X} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  SetLike.ext h

lemma mem_iff_abs_mem {I : VectorOrderIdeal X} {x : X} : x ∈ I ↔ |x| ∈ I := by
  constructor
  · exact I.abs_mem
  · intro h
    have : |x| ≤ abs |x| := by
      rw [abs_abs]
    exact I.solid this h

lemma sub_mem_sup_sub_sup_mem {I : VectorOrderIdeal X} {x y y' : X}
  (h : y - y' ∈ I) : x ⊔ y - x ⊔ y' ∈ I := by
  have : |x ⊔ y - x ⊔ y'| ≤ |y - y'| := by
    rw [sup_comm, sup_comm x y']
    exact abs_sup_sub_sup_le_abs y y' x
  exact I.solid this h


variable {Y : Type u} [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]

def comap (f : VecLatHom X Y) (Z : VectorOrderIdeal Y) :
    VectorOrderIdeal X :=
  {Submodule.comap f Z.toSubmodule with
    supClosed' := by
      intro a amem b bmem
      simp at amem bmem
      simp
      exact Z.supClosed amem bmem
    infClosed' := by
      intro a amem b bmem
      simp at amem bmem
      simp
      exact Z.infClosed amem bmem
    solid := by
      intro x y hxy ymem
      simp at ymem
      simp
      have : |f x| ≤ |f y| := by
        calc
          |f x| = f |x| := by rw [← f.map_abs x]
              _ ≤ f |y| := by exact f.monotone hxy
              _ = |f y| := by rw [f.map_abs y]
      exact Z.solid this ymem
  }

lemma mem_comap (f : VecLatHom X Y) (Z : VectorOrderIdeal Y) (x : X) :
    x ∈ comap f Z ↔ f x ∈ Z := by
  simp only [comap]
  rfl

/- def ker (f : VecLatHom X Y) : VectorOrderIdeal X := -/
/-   {LinearMap.ker f with -/
/-     supClosed' := by -/
/-       intro x xmem y ymem -/
/-       simp_all -/
/-     infClosed' := by -/
/-       intro x xmem y ymem -/
/-       simp_all -/
/-     solid := by -/
/-       intro x y hxy ymem -/
/-       simp -/
/-       simp at ymem -/
/-       rw [← abs_eq_zero_iff_zero] -/
/-       apply le_antisymm -/
/-       · calc -/
/-           |f x| = f |x| := by simp -/
/-               _ ≤ f |y| := by apply (f.monotone X Y) hxy -/
/-               _ = |f y| := by simp -/
/-               _ = 0     := by simp [ymem] -/
/-       · exact abs_nonneg _ -/
/-   } -/
end VectorOrderIdeal
