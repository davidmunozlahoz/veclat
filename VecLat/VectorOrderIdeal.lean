import VecLat.Basic

universe u

variable {X : Type u} [VectorLattice X]

structure VectorSublattice (X : Type u) [VectorLattice X] : Type u
  extends Submodule ℝ X, Sublattice X

namespace VectorSublattice

instance instSetLike : SetLike (VectorSublattice X) X where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s; cases t; congr; exact SetLike.coe_injective' h

instance instAddCommGroup (Y : VectorSublattice X) : AddCommGroup Y :=
  Y.toAddSubgroup.toAddCommGroup

instance instVectorLattice (Y : VectorSublattice X) : VectorLattice Y :=
  {
  toAddCommGroup := inferInstance
  toLattice := Y.instLatticeCoe
  toModule := Y.module
  add_le_add_left := by
    intros a b h c
    have : (a:X) ≤ (b:X) := h
    calc
      a + c = ↑ a + ↑ c := by simp
          _ ≤ ↑ b + ↑ c := by apply add_le_add_left this ↑c
          _ = b + c := by simp
  smul_le_smul_of_nonneg_left := by
    intros a ha b b' hbs
    have : (b:X) ≤ (b':X) := hbs
    calc
      a • b = a • (b:X) := by simp
          _ ≤ a • (b':X) := by exact smul_le_smul_of_nonneg_left this ha
          _ = a • b' := by simp
  smul_le_smul_of_nonneg_right := by
    intros b hb a a' has
    calc
      a • b = a • (b:X) := by simp
          _ ≤ a' • (b:X) := by exact smul_le_smul_of_nonneg_right has hb
          _ = a' • b := by simp
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

end VectorSublattice

structure VectorOrderIdeal (X : Type u) [VectorLattice X] : Type u
  extends VectorSublattice X where
  solid : ∀ {x y : X}, |x| ≤ |y| → y ∈ carrier → x ∈ carrier

namespace VectorOrderIdeal

instance instSetLike : SetLike (VectorOrderIdeal X) X where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s; cases t; congr; exact SetLike.coe_injective' h

lemma mem_iff_abs_mem {I : VectorOrderIdeal X} {x : X} : x ∈ I ↔ |x| ∈ I := by
  constructor
  · exact I.abs_mem
  · intro h
    have : |x| ≤ abs |x| := by
      rw [abs_abs]
    exact I.solid this h

end VectorOrderIdeal
