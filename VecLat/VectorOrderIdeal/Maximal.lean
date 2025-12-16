import VecLat.VectorOrderIdeal.Lattice
import VecLat.VectorOrderIdeal.Quotient
import VecLat.VectorOrderIdeal.PrincipalIdeal

variable {X : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

namespace Maximal

variable (I : VectorOrderIdeal X)

class IsMaximal : Prop where
  out : IsCoatom I

variable [IsMaximal I]

theorem le_iff {J : VectorOrderIdeal X} : I ≤ J ↔ J = ⊤ ∨ J = I := by
  have : IsCoatom I := IsMaximal.out
  exact IsCoatom.le_iff this

theorem trivial_ideals (J : VectorOrderIdeal (X ⧸ I)) : (J = ⊥) ∨ (J = ⊤) := by
  let J' := VectorOrderIdeal.comap (Quotient.mkQ I) J
  have map : (I.mkQ)'' J' = J := by
    dsimp only [J']
    change (I.mkQ)'' ((I.mkQ)⁻¹' J) = J
    exact Set.image_preimage_eq J
      (Submodule.Quotient.mk_surjective I.toSubmodule)
  have : I ≤ J' := by
    intro x hx
    change x ∈ J'
    rw [VectorOrderIdeal.mem_comap (Quotient.mkQ I) J x]
    change I.mkQ x ∈ J
    have : I.mkQ x = 0 :=
      (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr hx
    rw [this]
    exact Submodule.zero_mem J.toSubmodule
  have : _ := ((le_iff I).mp this)
  cases this with
    | inl h =>
      right
      apply SetLike.coe_set_eq.mp
      rw [← map, h]
      exact Set.image_univ_of_surjective
            (Submodule.Quotient.mk_surjective I.toSubmodule)
    | inr h =>
      left
      apply SetLike.coe_set_eq.mp
      rw [← map, h]
      ext x
      constructor
      · intro xmem
        obtain ⟨y, hy1, hy2⟩ := xmem
        change x ∈ (⊥ : VectorOrderIdeal (X⧸I))
        rw [@VectorOrderIdeal.mem_bot, ← hy2]
        exact (Submodule.Quotient.mk_eq_zero (I.toSubmodule)).mpr hy1
      · intro xmem
        apply (Submodule.mem_bot ℝ).mp at xmem
        rw [xmem]
        use 0
        constructor
        · exact Submodule.zero_mem I.toSubmodule
        · apply Submodule.Quotient.mk_zero

instance instArchimedean : Archimedean (X ⧸ I) where
  arch := by
    intro x y ypos
    let J := PrincipalIdeal.instVectorOrderIdeal y
    have trivial_ideals := trivial_ideals I J
    have : y ∈ J := PrincipalIdeal.gen_mem y (le_of_lt ypos)
    have : J = ⊤ := by
      cases trivial_ideals with
        | inl h =>
            rw [h] at this
            rw [VectorOrderIdeal.mem_bot] at this
            rw [this] at ypos
            exact (StrictMono.apply_eq_top_iff fun ⦃a b⦄ a_1 ↦ ypos).mp rfl
        | inr h => exact h
    have : x ∈ J := by rw [this]; trivial
    obtain ⟨t, ht1, ht2⟩ := this
    obtain ⟨n, hn⟩ := exists_nat_gt t
    use n
    calc
      x ≤ |x| := by rw [abs]; simp
      _ ≤ t • y := ht2
      _ ≤ ↑n • y := smul_le_smul_of_nonneg_right (le_of_lt hn) (le_of_lt ypos)
      _ = n • y := Nat.cast_smul_eq_nsmul ℝ n y

protected theorem le_total (x y : X ⧸ I) : x ≤ y ∨ y ≤ x := by
    let J : VectorOrderIdeal (X ⧸ I) :=
      PrincipalIdeal.instVectorOrderIdeal ( (x - y)⁻ )
    have := (trivial_ideals I) J
    cases this with
      | inl h =>
        have : PrincipalIdeal ( (x - y)⁻ ) = ↑(⊥ : VectorOrderIdeal (X
        ⧸ I) ) := by
          rw [SetLike.ext'_iff] at h
          exact h
        rw [PrincipalIdeal.bot_iff_zero] at this
        · right
          simp at this
          assumption
        · exact negPart_nonneg (x - y)
      | inr h =>
        have : (x-y)⁺ ∈ J := by rw [h]; trivial
        have : (x-y)⁺ = 0 := PrincipalIdeal.posPart_notmem_PI_negPart (x-y) this
        left
        simp at this
        assumption

theorem one_dim_pos (x y : X)
  (xnonneg : 0 ≤ Quotient.mkQ I x) (ypos : 0 < Quotient.mkQ I y) :
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
          n • (x' - t • y') ≤ n • ((t+1/n)•y' - t • y') := by exact
                (smul_le_smul_of_nonneg_left temp (Nat.cast_nonneg n))
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

variable {e : X} (epos : 0 < Quotient.mkQ I e)

def real_map : VecLatHom ℝ (X ⧸ I) where
  toFun := fun t => t • Quotient.mkQ I e
  map_add' := by
    intro t s
    exact add_smul t s _
  map_smul' := by
    intro t s
    simp
    exact mul_smul t s ((Quotient.mkQ I) e)
  map_sup' := by
    intro t s
    exact sup_smul_nonneg ((Quotient.mkQ I) e) t s (le_of_lt epos)
  map_inf' := by
    intro t s
    exact inf_smul_nonneg ((Quotient.mkQ I) e) t s (le_of_lt epos)

omit [IsMaximal I] in
lemma real_map_injective : Function.Injective (real_map I epos) := by
  intro t s h
  change t • Quotient.mkQ I e = s • Quotient.mkQ I e at h
  have : 0 ≠ Quotient.mkQ I e := ne_of_lt epos
  have h : (t - s) • Quotient.mkQ I e = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h
  apply smul_eq_zero.mp at h
  cases h with
  | inl h' => rw [← sub_eq_zero]; assumption
  | inr h' => exact False.elim (this (id (Eq.symm h')))

lemma real_map_surjective : Function.Surjective (real_map I epos) := by
  intro a
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective I.toSubmodule a
  obtain ⟨t, ht⟩ := one_dim I x e epos
  use t
  rw [← hx]
  change t • Quotient.mkQ I e = Quotient.mkQ I x
  exact Eq.symm ht

lemma real_map_bijective : Function.Bijective (real_map I epos) :=
  ⟨real_map_injective I epos, real_map_surjective I epos⟩

noncomputable def character : VecLatHom X ℝ :=
  VecLatHom.comp (VecLatHom.symm (real_map I epos)
  (real_map_bijective I epos)) (Quotient.mkQ I)

theorem character_basis : (character I epos) e = 1 := by
  rw [character, VecLatHom.comp_apply, VecLatHom.symm_apply]
  change (Quotient.mkQ I) e = (1:ℝ) • (Quotient.mkQ I) e
  simp

theorem character_eval_I (x : X) (xmem : x ∈ I) : (character I epos) x = 0 := by
  rw [character, VecLatHom.comp_apply, VecLatHom.symm_apply]
  change I.mkQ x = (0:ℝ) • (Quotient.mkQ I) e
  simp
  assumption

end Maximal
