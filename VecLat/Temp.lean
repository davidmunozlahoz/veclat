import VecLat.Maximal

open Maximal

variable {X : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

variable (I : VectorOrderIdeal X) [IsMaximal I]

theorem one_dim_pos (x y : X)
  (xnonneg : 0 ≤ Quotient.mkQ I x) (ypos : 0 < Quotient.mkQ I y):
  ∃ t : ℝ, Quotient.mkQ I x = t • Quotient.mkQ I y := by
    let x' := Quotient.mkQ I x
    let y' := Quotient.mkQ I y
    let T := { s : ℝ | 0 ≤ s ∧ x' ≤ s • y' }
    have nonempty : T.Nonempty := by
      obtain ⟨n, hn⟩ := Archimedean.arch x' ypos
      use n
      constructor
      · exact Nat.cast_nonneg n
      · unfold y'
        exact hn.trans
          (by norm_cast : n • Quotient.mkQ I y ≤ (↑n : ℝ) • Quotient.mkQ I y)
    have bddbelow : BddBelow T := by
      use 0
      intro s hs
      exact hs.1
    let t := sInf T
    have h1 (n : ℕ) (hn : 1 ≤ n) : (t - 1/n) • y' ≤ x' := by
      by_cases hpos : 0 ≤ t - 1/n
      · cases Maximal.le_total I ( (t - 1/n) • y') x' with
          | inl h => exact h
          | inr h =>
            have : t - 1/n ∈ T := ⟨hpos, h⟩
            have : t ≤ t - 1/n := csInf_le bddbelow this
            simp at this
            rw [this] at hn
            contradiction
      · push_neg at hpos
        calc
          (t - 1/n) • y' ≤ (0:ℝ) • y' := by exact
                smul_le_smul_of_nonneg_right (le_of_lt hpos) (le_of_lt ypos)
                       _ = 0 := by simp
                       _ ≤ x' := xnonneg
    have h1' (n : ℕ) : n • (t • y' - x') ≤ y' := by
      by_cases zero : n = 0
      · rw [zero]; simp; exact le_of_lt ypos
      · have : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr zero
        have := h1 n this
        have temp : (t-1/n)•y' + (1/n:ℝ)•y' - x' ≤ (1/n:ℝ) • y' := by
          rw [add_comm, add_sub_assoc]
          nth_rw 2 [← add_zero ((1 / (n:ℝ)) • y')]
          apply add_le_add
          · exact le_refl _
          · rw [sub_eq_add_neg, add_neg_nonpos_iff]
            exact this
        calc
          n • (t • y' - x') = n • ((t-1/n)•y' + (1/n:ℝ)•y' - x') := by
            congr
            rw [sub_smul, sub_eq_add_neg, add_assoc]
            simp
                          _ ≤ n • ( (1/n:ℝ)•y' ) := by exact
                            smul_le_smul_of_nonneg_left temp (Nat.cast_nonneg n)
                          _ = (n:ℝ) • ( (1/n:ℝ)•y' ) := by norm_cast
                          _ = y' := by
                                      rw [smul_smul]
                                      field_simp [zero]
                                      simp
    have h1'' : t • y' ≤ x' := by
      obtain j := arch' h1'
      exact tsub_nonpos.mp j
    have h2 (n : ℕ) (hn : 1 ≤ n) : (t + 1/n) • y' ≥ x' := by
      have : t < t + 1/n := by simp; exact hn
      obtain ⟨s, hs1, hs2⟩ := (csInf_lt_iff bddbelow nonempty).mp this
      calc
        x' ≤ s • y' := by exact hs1.2
         _ ≤ (t + 1/n) • y' := by exact smul_le_smul_of_nonneg_right (le_of_lt hs2) (le_of_lt ypos)
    have h2' (n : ℕ) : n • (x' - t• y') ≤ y' := by
      by_cases zero : n = 0
      · rw [zero]; simp; exact le_of_lt ypos
      · have : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr zero
        have temp : x' - t • y' ≤ (t+1/n)•y' - t • y' := by
          apply sub_le_sub
          · exact h2 n this
          · exact le_refl _
        calc
          n • (x' - t • y') ≤ n • ((t+1/n)•y' - t • y') := by exact smul_le_smul_of_nonneg_left temp (Nat.cast_nonneg n)
                          _ = n • ( (1/n:ℝ)•y' ) := by
                              congr
                              rw [add_smul, add_sub_assoc,
                              add_comm, sub_add]
                              simp
                          _ = (n:ℝ) • ( (1/n:ℝ)•y' ) := by norm_cast
                          _ = y' := by
                                      rw [smul_smul]
                                      field_simp [zero]
                                      simp
    have h2'' : x' ≤ t • y' := by
      obtain j := arch' h2'
      exact tsub_nonpos.mp j
    use t
    exact le_antisymm h2'' h1''

theorem one_dim (x y : X) (ypos : 0 < Quotient.mkQ I y) :
    ∃ t : ℝ, Quotient.mkQ I x = t • Quotient.mkQ I y := by
  let x' := Quotient.mkQ I x
  let y' := Quotient.mkQ I y
  cases Maximal.le_total I x' 0 with
  | inl x'nonpos =>
    have : 0 ≤ Quotient.mkQ I (-x) := by
      simp; exact x'nonpos
    obtain ⟨t, ht⟩ := one_dim_pos I (-x) y this ypos
    use -t
    simp at ht
    simp
    rw [← ht]
    simp
  | inr x'nonneg =>
    exact one_dim_pos I x y x'nonneg ypos
