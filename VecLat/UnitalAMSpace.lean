import VecLat.Basic

set_option linter.unusedSectionVars false

class UnitalAMSpace (X : Type*) (e : X) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  pos : 0 ≤ e
  unit : ∀ x : X, ∃ s : ℝ, 0 ≤ s ∧ |x| ≤ s • e

namespace UnitalAMSpace

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] (e : X) [UnitalAMSpace X e]

variable (x : X)

noncomputable section

theorem unit_def : ∃ s : ℝ, 0 ≤ s ∧ |x| ≤ s • e := by
  exact UnitalAMSpace.unit x

theorem unit_pos : 0 ≤ e := by
  exact UnitalAMSpace.pos

def S := { s : ℝ | 0 ≤ s ∧ |x| ≤ s • e }

lemma S_nonempty : (S e x).Nonempty := by
  obtain ⟨s, hs⟩ := unit_def e x
  use s
  exact hs

lemma S_bddbelow : BddBelow (S e x) := by
  use 0
  intro s hs
  exact hs.1

def norm : X → ℝ :=
  fun x => sInf (S e x)

lemma norm_def : norm e x = sInf (S e x) := rfl

lemma norm_nonneg : 0 ≤ norm e x := by
  rw [norm_def]
  apply Real.le_sInf
  · intro s hs
    exact hs.1
  · simp

lemma gt_norm (t : ℝ) (h : norm e x < t) : |x| ≤ t • e := by
  rw [norm_def] at h
  rw [csInf_lt_iff (S_bddbelow e x) (S_nonempty e x)] at h
  obtain ⟨b, hbS, hbt⟩ := h
  calc
    |x| ≤ b • e := by exact hbS.2
      _ ≤ t • e := by
        apply smul_le_smul_of_nonneg_right (le_of_lt hbt) (unit_pos e)
end

variable [Archimedean X]

lemma norm_attained : |x| ≤ (norm e x) • e := by
  have h : ∀ t : ℝ, 0 < t → |x| ≤ ((norm e x) + t) • e := by
    intro t ht
    exact gt_norm e x ((norm e x) + t) (by norm_num [ht])
  have h' : ∀ t : ℝ, 0 ≤ t →  t • (|x| - (norm e x) • e) ≤ e := by
    intro t ht
    by_cases ht' : t = 0
    · simp [ht', unit_pos e]
    · have tpos : 0 < t := by
        apply lt_of_le_of_ne ht (by simp; simpa [eq_comm] using ht')
      have tinvpos : 0 < t⁻¹ := by
        rw [inv_pos]
        exact tpos
      have : |x| - (norm e x) • e ≤ t⁻¹ • e := by
        calc
          |x| - (norm e x) • e ≤ (norm e x + t⁻¹) • e - (norm e x) • e := by
              apply sub_le_sub
              · exact h t⁻¹ tinvpos
              · simp
                              _= t⁻¹ • e := by rw [add_smul]; simp
      calc
        t • (|x| - (norm e x) • e) ≤ t • (t⁻¹ • e) := by
                apply smul_le_smul_of_nonneg_left this ht
            _ = e := by rw [← smul_assoc]; simp [ht']
  have hnat : ∀ n : ℕ, n • (|x| - (norm e x) • e) ≤ e := by
    intro n
    calc
      n • (|x| - (norm e x) • e) = (n:ℝ) • (|x| - (norm e x) • e) :=
        by apply Eq.symm ( Nat.cast_smul_eq_nsmul ℝ n (|x| - norm e x • e) )
        _ ≤ e := by apply h' (n:ℝ) (Nat.cast_nonneg n)
  have : |x| - (norm e x) • e ≤ 0 := arch' hnat
  have : _ := add_le_add_right this ((norm e x) • e)
  simp at this
  simp
  exact this

lemma norm_zero_iff_zero : norm e x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : |x| ≤ (0:ℝ) • e := by
      rw [← h]
      apply norm_attained e x
    rw [zero_smul] at this
    rw [← abs_eq_zero_iff_zero]
    apply le_antisymm this (abs_nonneg x)
  · intro h
    apply le_antisymm
    · have hc : 0 ∈ S e x := by
        constructor
        · exact le_refl 0
        · rw [h, zero_smul, abs_zero]
      apply csInf_le (S_bddbelow e x) hc
    · exact norm_nonneg e x

lemma norm_smul (r : ℝ) : norm e (r•x) = |r| • (norm e x) := by
  sorry

lemma norm_add (y : X) : norm e (x + y) ≤ norm e x + norm e y := by
  have : norm e x + norm e y ∈ S e (x + y) := by
    constructor
    · apply add_nonneg (norm_nonneg e x) (norm_nonneg e y)
    · calc
        |x + y| ≤ |x| + |y| := by exact abs_add_le x y
              _ ≤ (norm e x) • e + (norm e y) • e :=
              by exact add_le_add (norm_attained e x) (norm_attained e y)
              _ = (norm e x + norm e y) • e := by rw [add_smul]
  exact csInf_le (S_bddbelow e (x+y)) this

lemma norm_le (y : X) (hxy : |x| ≤ |y|) : norm e x ≤ norm e y := by
  have : norm e y ∈ S e x := by
    constructor
    · exact norm_nonneg e y
    · apply le_trans hxy
      exact norm_attained e y
  exact csInf_le (S_bddbelow e x) this

lemma AMnorm (y : X) (xpos : 0 ≤ x) (ypos : 0 ≤ y) :
      norm e (x ⊔ y) = (norm e x) ⊔ (norm e y) := by
      have sup_eq_abs : |x ⊔ y| = x ⊔ y := by
        apply abs_of_nonneg
        apply le_sup_of_le_left
        exact xpos
      apply le_antisymm
      · have : max (norm e x) (norm e y) ∈ S e (x ⊔ y) := by
          constructor
          · rw [le_max_iff]
            constructor
            exact norm_nonneg e x
          · calc
              |x ⊔ y| = x ⊔ y := by exact sup_eq_abs
                    _ = |x| ⊔ |y| := by
                      congr; · symm; · exact abs_of_nonneg xpos
                      symm; exact abs_of_nonneg ypos
                    _ ≤ (norm e x)•e ⊔ |y| := by
                      apply sup_le_sup_right (norm_attained e x) |y|
                    _ ≤ (norm e x)•e ⊔ (norm e y)•e := by
                      apply sup_le_sup_left
                            (norm_attained e y)
                            ((norm e x)•e)
                    _ ≤ ((norm e x) ⊔ (norm e y))•e := by
                      apply sup_le
                      · apply smul_le_smul_of_nonneg_right
                        · exact le_max_left (norm e x) (norm e y)
                        · exact unit_pos e
                      · apply smul_le_smul_of_nonneg_right
                        · exact le_max_right (norm e x) (norm e y)
                        · exact unit_pos e
        exact csInf_le (S_bddbelow e (x ⊔ y)) this
      · have hx : |x| ≤ |x ⊔ y| := by
          calc
            |x| = x := by exact abs_of_nonneg xpos
              _ ≤ x ⊔ y := by exact le_sup_left
              _ = |x ⊔ y| := by symm; exact sup_eq_abs
        have hy : |y| ≤ |x ⊔ y| := by
          calc
            |y| = y := by exact abs_of_nonneg ypos
              _ ≤ x ⊔ y := by exact le_sup_right
              _ = |x ⊔ y| := by symm; exact sup_eq_abs
        apply max_le
        · exact norm_le e x (x ⊔ y) hx
        · exact norm_le e y (x ⊔ y) hy

instance instSeminormedAddCommGroup : SeminormedAddCommGroup X := sorry

instance instNormedSpace : NormedSpace ℝ X := sorry

end UnitalAMSpace
