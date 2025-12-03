import VecLat.VectorOrderIdeal

universe u

variable {X : Type u} [VectorLattice X]

def PrincipalOrderIdeal (a : X) := {x : X | ∃ s : ℝ, 0 ≤ s ∧ |x| ≤ s • a}

namespace PrincipalOrderIdeal

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
        |x + y| ≤ |x| + |y| := abs_add_le x y
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

instance instSublattice : VectorSublattice X :=
  VectorSublattice.ofSubmoduleAbs (instSubmodule a) (by
    rintro x ⟨s, hs⟩
    use s
    constructor
    · exact hs.1
    · rw [abs_abs x]
      exact hs.2)

instance instOrderIdeal : VectorOrderIdeal X := { instSublattice a with
    solid := by
      rintro x y hxy ⟨s, hs⟩
      use s
      constructor
      · exact hs.1
      · calc
          |x| ≤ |y| := hxy
          _ ≤ s • a := hs.2 }

instance instVectorLattice : VectorLattice (PrincipalOrderIdeal a) :=
  (inferInstance : VectorLattice (instSublattice a))


def gen_mem {apos : 0 ≤ a} : a ∈ PrincipalOrderIdeal a := by
  use 1
  constructor
  · exact zero_le_one
  · rw [one_smul]
    rw [abs_of_nonneg apos]

noncomputable section

variable {x y : X}
variable {apos : 0 ≤ a}

def S (a x : X) := { s : ℝ | 0 ≤ s ∧ |x| ≤ s • a }

lemma S_nonempty (xmem : x ∈ PrincipalOrderIdeal a) : (S a x).Nonempty := by
  obtain ⟨s, hs⟩ := xmem
  use s
  exact hs

lemma S_bddbelow : BddBelow (S a x) := by
  use 0
  intro s hs
  exact hs.1

def norm : X → ℝ :=
  fun x => sInf (S a x)

lemma norm_def : norm a x = sInf (S a x) := rfl

lemma norm_nonneg (x : X) : 0 ≤ norm a x := by
  rw [norm_def]
  apply Real.le_sInf
  · intro s hs
    exact hs.1
  · simp

lemma gt_norm (apos : 0 ≤ a) (x : X) (t : ℝ) (xmem : x ∈ PrincipalOrderIdeal a)
  (h : norm a x < t) : |x| ≤ t • a := by
  rw [norm_def] at h
  rw [csInf_lt_iff (S_bddbelow a) (S_nonempty a xmem)] at h
  obtain ⟨b, hbS, hbt⟩ := h
  calc
    |x| ≤ b • a := by exact hbS.2
      _ ≤ t • a := by apply smul_le_smul_of_nonneg_right (le_of_lt hbt) apos

variable [Archimedean X]

lemma norm_attained (apos : 0 ≤ a) (xmem : x ∈ PrincipalOrderIdeal a) : |x| ≤ (norm a x) • a := by
  have h : ∀ t : ℝ, 0 < t → |x| ≤ ((norm a x) + t) • a := by
    intro t ht
    exact gt_norm a apos x ((norm a x) + t) xmem (by norm_num [ht])

  have h' : ∀ t : ℝ, 0 ≤ t →  t • (|x| - (norm a x) • a) ≤ a := by
    intro t ht
    by_cases ht' : t = 0
    · simp [ht', apos]
    · have tpos : 0 < t := by
        apply lt_of_le_of_ne ht (by simp; simpa [eq_comm] using ht')
      have tinvpos : 0 < t⁻¹ := by
        rw [inv_pos]
        exact tpos
      have : |x| - (norm a x) • a ≤ t⁻¹ • a := by
        calc
          |x| - (norm a x) • a ≤ (norm a x + t⁻¹) • a - (norm a x) • a := by
              apply sub_le_sub
              · exact h t⁻¹ tinvpos
              · simp
                              _= t⁻¹ • a := by rw [add_smul]; simp
      calc
        t • (|x| - (norm a x) • a) ≤ t • (t⁻¹ • a) := by
                apply smul_le_smul_of_nonneg_left this ht
            _ = a := by rw [← smul_assoc]; simp [ht']

  have hnat : ∀ n : ℕ, n • (|x| - (norm a x) • a) ≤ a := by
    intro n
    calc
      n • (|x| - (norm a x) • a) = (n:ℝ) • (|x| - (norm a x) • a) :=
        by apply Eq.symm ( Nat.cast_smul_eq_nsmul ℝ n (|x| - norm a x • a) )
        _ ≤ a := by apply h' (n:ℝ) (Nat.cast_nonneg n)

  have : |x| - (norm a x) • a ≤ 0 := arch' hnat

  have : _ := add_le_add_right this ((norm a x) • a)
  simp at this
  simp
  exact this

lemma norm_zero_iff_zero (apos : 0 ≤ a) (xmem : x ∈ PrincipalOrderIdeal a) :
    norm a x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : |x| ≤ (0:ℝ) • a := by
      rw [← h]
      apply norm_attained a apos xmem
    rw [zero_smul] at this
    rw [← abs_eq_zero_iff_zero]
    apply le_antisymm this (abs_nonneg x)
  · intro h
    apply le_antisymm
    · have hc : 0 ∈ S a x := by
        constructor
        · exact le_refl 0
        · rw [h, zero_smul, abs_zero]
      apply csInf_le (S_bddbelow a) hc
    · exact norm_nonneg a x

/- lemma norm_smul (apos : 0 ≤ a) (xmem : x ∈ PrincipalOrderIdeal a) (r : ℝ) : -/
/-       norm a (r•x) = |r| • (norm a x) := by sorry -/

lemma norm_add (apos : 0 ≤ a)
      (xmem : x ∈ PrincipalOrderIdeal a) (ymem : y ∈ PrincipalOrderIdeal a) :
      norm a (x + y) ≤ norm a x + norm a y := by
  have : norm a x + norm a y ∈ S a (x + y) := by
    constructor
    · apply add_nonneg (norm_nonneg a x) (norm_nonneg a y)
    · calc
        |x + y| ≤ |x| + |y| := by exact abs_add_le x y
              _ ≤ (norm a x) • a + (norm a y) • a :=
              by exact add_le_add (norm_attained a apos xmem) (norm_attained a apos ymem)
              _ = (norm a x + norm a y) • a := by rw [add_smul]
  exact csInf_le (S_bddbelow a) this

end

end PrincipalOrderIdeal
