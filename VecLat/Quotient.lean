import VecLat.Basic
import VecLat.VectorOrderIdeal
import VecLat.Hom

import Mathlib.LinearAlgebra.Quotient.Defs

namespace Quotient

variable {X I : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X] (I : VectorOrderIdeal X)

instance instHasQuotient : HasQuotient X (VectorOrderIdeal X) where
  quotient' := fun (I : VectorOrderIdeal X) => Quotient I.quotientRel

instance instAddCommGroup : AddCommGroup (X ⧸ I) :=
  Submodule.Quotient.addCommGroup I.toSubmodule

instance instModule : Module ℝ (X ⧸ I) :=
  Submodule.Quotient.module I.toSubmodule

def quot_sup : X⧸I → X⧸I → X⧸I := by
    let f : X → X → X⧸I := fun x y => I.mkQ (x ⊔ y)
    have wd (x : X) : ∀ (y y' : X), I.quotientRel y y' → f x y = f x y' := by
      intro y y' rel
      rw [Submodule.quotientRel_def] at rel
      dsimp [f]
      rw [Submodule.Quotient.eq I.toSubmodule]
      exact VectorOrderIdeal.sub_mem_sup_sub_sup_mem rel
    let f₂ : X → X⧸I → X⧸I := fun x => Quotient.lift (f x) (wd x)
    have wd₂ : ∀ (x x' : X), I.quotientRel x x' → f₂ x = f₂ x' := by
      intro x x' rel
      ext y
      obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_surjective I.toSubmodule) y
      rw [← ha]
      dsimp [f₂,Quotient.lift,Submodule.Quotient.mk,f]
      rw [Quotient.eq'',Submodule.quotientRel_def]
      rw [Submodule.quotientRel_def] at rel
      rw [sup_comm, sup_comm x']
      exact VectorOrderIdeal.sub_mem_sup_sub_sup_mem rel
    let f₃ : X⧸I → X⧸I → X⧸I := Quotient.lift f₂ wd₂
    exact f₃

lemma mkQ_map_sup {x y : X} : I.mkQ (x ⊔ y) = quot_sup I (I.mkQ x) (I.mkQ y) := by
  dsimp [quot_sup,Quotient.lift,Submodule.Quotient.mk]

instance instLattice : Lattice (X ⧸ I) where
  le := fun a b => ∃ x : X, (0 ≤ x) ∧ (I.mkQ x = b - a)
  le_refl := by
    intro a
    use 0
    constructor
    · exact le_refl 0
    · simp
  le_trans := by
    intro a b c ⟨x, hx, hxab⟩ ⟨y, hy, hybc⟩
    use x+y
    constructor
    · exact Left.add_nonneg hx hy
    · rw [Submodule.mkQ_apply] at hxab hybc
      simp [hxab, hybc]
  le_antisymm := by
    intro a b ⟨x, hx, hxab⟩ ⟨y, hy, hyba⟩
    have xymem : x+y ∈ I.toSubmodule := by
      rw [← @Submodule.Quotient.mk_eq_zero ℝ X (x+y) _ _ _ I.toSubmodule]
      rw [Submodule.mkQ_apply] at hxab hyba
      simp [hxab, hyba]
    have : |x| ≤ |x+y| := by
      calc
        |x| = x := by exact abs_of_nonneg hx
          _ ≤ x + y := by exact (le_add_iff_nonneg_right x).mpr hy
          _ = |x + y| := by rw [abs_of_nonneg (add_nonneg hx hy)]
    have xmem : x ∈ I.toSubmodule := by
      exact I.solid this xymem
    rw [← @Submodule.Quotient.mk_eq_zero ℝ X x _ _ _ I.toSubmodule] at xmem
    rw [Submodule.mkQ_apply] at hxab
    rw [xmem] at hxab
    exact Eq.symm (sub_eq_zero.mp (Eq.symm hxab))
  sup := quot_sup I
  le_sup_left := by
    intro a b
    obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_surjective I.toSubmodule) a
    obtain ⟨y,hy⟩ := (Submodule.Quotient.mk_surjective I.toSubmodule) b
    use x ⊔ y - x
    constructor
    · simp
    · rw [← hx, ← hy, ← Submodule.mkQ_apply,
          ← Submodule.mkQ_apply, ← mkQ_map_sup]
      simp
  le_sup_right := by
    intro a b
    obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_surjective I.toSubmodule) a
    obtain ⟨y,hy⟩ := (Submodule.Quotient.mk_surjective I.toSubmodule) b
    use x ⊔ y - y
    constructor
    · simp
    · rw [← hx, ← hy, ← Submodule.mkQ_apply,
          ← Submodule.mkQ_apply, ← mkQ_map_sup ]
      simp
  sup_le := by sorry
  inf := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (X ⧸ I) where
  add_le_add_left := by
    intro a b hab c
    obtain ⟨x, xpos, hxab⟩ := hab
    use x
    constructor
    · exact xpos
    · simp [hxab]

instance instVectorLattice : VectorLattice (X ⧸ I) where
  smul_le_smul_of_nonneg_left := by
    intro t tpos a b hab
    obtain ⟨x, xpos, hxab⟩ := hab
    use t • x
    constructor
    · exact smul_nonneg tpos xpos
    · simp [hxab]
      exact smul_sub t b a

def mkQ : VecLatHom X (X ⧸ I) := {
  I.mkQ with
    map_sup' := by sorry
    map_inf' := by sorry
  }

end Quotient
