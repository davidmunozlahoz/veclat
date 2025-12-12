import VecLat.Basic
import VecLat.VectorOrderIdeal
import VecLat.UnitalAMSpace
import VecLat.Lattice

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

def PrincipalIdeal (a : X) := {x : X | ∃ s : ℝ, 0 ≤ s ∧ |x| ≤ s • a}

namespace PrincipalIdeal

variable (a : X)

instance instSubmodule : Submodule ℝ X where
  carrier := { x : X | ∃ s : ℝ, 0 ≤ s ∧ |x| ≤ s • a }
  zero_mem' := by
    use 0; simp
  add_mem' := by
    rintro x y ⟨s1, hs1⟩ ⟨s2, hs2⟩
    use s1 + s2
    constructor
    · linarith
    · calc
        |x + y| ≤ |x| + |y| := by exact abs_add_le x y
        _ ≤ s1 • a + s2 • a := add_le_add hs1.2 hs2.2
        _ = (s1 + s2) • a := by rw [add_smul]
  smul_mem' := by
    rintro r x ⟨s, hs⟩
    use |r| * s
    constructor
    · apply mul_nonneg
      · exact abs_nonneg r
      · exact hs.1
    · calc
      |r • x| = |r| • |x| := abs_smul'
      _ ≤ |r| • (s • a) := smul_le_smul_of_nonneg_left hs.2 (abs_nonneg r)
      _ = (|r| * s) • a := by rw [mul_smul]

instance instVectorSublattice : VectorSublattice X :=
  VectorSublattice.ofSubmoduleAbs (instSubmodule a) (by
    rintro x ⟨s, hs⟩
    use s
    constructor
    · exact hs.1
    · rw [abs_abs x]
      exact hs.2)

instance instVectorOrderIdeal : VectorOrderIdeal X := { instVectorSublattice a with
    solid := by
      rintro x y hxy ⟨s, hs⟩
      use s
      constructor
      · exact hs.1
      · calc
          |x| ≤ |y| := hxy
          _ ≤ s • a := hs.2 }

instance instAddCommGroup : AddCommGroup (PrincipalIdeal a) :=
  (inferInstance : AddCommGroup (instVectorSublattice a))

instance instLattice : Lattice (PrincipalIdeal a) :=
  (inferInstance : Lattice (instVectorSublattice a))

instance instIsOrderedAddMonoid : IsOrderedAddMonoid (PrincipalIdeal a) :=
  (inferInstance : IsOrderedAddMonoid (instVectorSublattice a))

instance instVectorLattice : VectorLattice (PrincipalIdeal a) :=
  (inferInstance : VectorLattice (instVectorSublattice a))

lemma gen_mem (apos : 0 ≤ a) : a ∈ PrincipalIdeal a := by
  use 1
  constructor
  · exact zero_le_one
  · rw [one_smul]
    rw [abs_of_nonneg apos]

lemma disjoint_not_mem (h : a₊ ∈ PrincipalIdeal (a₋)) : a₊ = 0 := by
  /- use and prove disjoint_smul -/
  sorry

lemma bot_iff_zero : PrincipalIdeal a = (⊥ : VectorOrderIdeal X) ↔ a = 0 := by sorry
/- def gen_type (apos : 0 ≤ a) : PrincipalIdeal a := ⟨a, gen_mem a apos⟩ -/
/- TO DO: show that every PrincipalIdeal a is an instance of
   IsUnitalAMSpace -/

end PrincipalIdeal
