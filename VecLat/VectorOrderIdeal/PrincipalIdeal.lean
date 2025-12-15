import VecLat.VectorOrderIdeal.Basic
import VecLat.VectorOrderIdeal.Lattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
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
      |r • x| = |r| • |x| := abs_smul' x r
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

theorem gen_mem (apos : 0 ≤ a) : a ∈ PrincipalIdeal a := by
  use 1
  constructor
  · exact zero_le_one
  · rw [one_smul]
    rw [abs_of_nonneg apos]

theorem posPart_notmem_PI_negPart (h : a⁺ ∈ PrincipalIdeal (a⁻)) : a⁺ = 0 := by
  obtain ⟨s, hs1, hs2⟩ := h
  apply le_antisymm
  · calc
      a⁺ = a⁺ ⊓ |a⁺| := by simp [abs]
       _ ≤ a⁺ ⊓ (s • a⁻) := by
          apply inf_le_inf
          · rfl
          · exact hs2
       _ = (s • a⁻) ⊓ a⁺ := by exact inf_comm a⁺ _
       _ = 0 := disjoint_smul a⁻ a⁺ s hs1
                (by rw [inf_comm]; exact posPart_inf_negPart_eq_zero a)
  · exact posPart_nonneg a

theorem bot_iff_zero (apos : 0 ≤ a) : PrincipalIdeal a = (⊥ : VectorOrderIdeal X) ↔ a = 0 := by
  constructor
  · intro h
    have : a ∈ (⊥ : VectorOrderIdeal X) := by
      change a ∈ ((⊥ : VectorOrderIdeal X) : Set X)
      rw [← h]
      exact gen_mem a apos
    change a ∈ (⊥ : Submodule ℝ X) at this
    rw [Submodule.mem_bot] at this
    assumption
  · intro h
    rw [h]
    ext x
    constructor
    · intro h'
      change x ∈ (⊥ : Submodule ℝ X)
      rw [Submodule.mem_bot]
      obtain ⟨s, hs1, hs2⟩ := h'
      simp at hs2
      have : |x| = 0 := le_antisymm hs2 (abs_nonneg x)
      exact (abs_eq_zero_iff_zero x).mp this
    · intro h'
      change x ∈ (⊥ : Submodule ℝ X) at h'
      rw [Submodule.mem_bot] at h'
      rw [h']
      exact gen_mem 0 (le_refl 0)

end PrincipalIdeal
