import VecLat.Quotient
import VecLat.Lattice
import VecLat.UnitalAMSpace
import VecLat.VectorOrderIdeal
import VecLat.PrincipalIdeal

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
      x ≤ |x| := by simp
      _ ≤ t • y := ht2
      _ ≤ ↑n • y := smul_le_smul_of_nonneg_right (le_of_lt hn) (le_of_lt ypos)
      _ = n • y := Nat.cast_smul_eq_nsmul ℝ n y

protected lemma le_total (x y : X ⧸ I) : x ≤ y ∨ y ≤ x := by
    let J : VectorOrderIdeal (X ⧸ I) :=
      PrincipalIdeal.instVectorOrderIdeal ( (x - y)₋ )
    have := (trivial_ideals I) J
    cases this with
      | inl h =>
        have : PrincipalIdeal ( (x - y)₋ ) = ↑(⊥ : VectorOrderIdeal (X
        ⧸ I) ) := by
          rw [SetLike.ext'_iff] at h
          exact h
        rw [PrincipalIdeal.bot_iff_zero] at this
        right
        rw [← negp_sub_eq_zero_iff, this]
      | inr h =>
        have : (x-y)₊ ∈ J := by rw [h]; trivial
        have : (x-y)₊ = 0 := PrincipalIdeal.disjoint_not_mem (x-y) this
        left
        rw [← posp_sub_eq_zero_iff, this]

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

end Maximal

namespace UnitalAMSpace

variable (e : X) [IsUnitalAMSpace X e]

open VectorOrderIdeal

variable (I : VectorOrderIdeal X)

lemma top_iff_unit_mem : I = ⊤ ↔ e ∈ I := by
  constructor
  · intro h; rw [h]; trivial
  · intro h
    ext x
    constructor
    · intro; trivial
    · intro hx
      obtain ⟨s, hs1, hs2⟩ := unit_def e x
      have : 0 ≤ s • e := by
        calc
          0 = s • 0 := by simp
          _ ≤ s • e := by exact smul_le_smul_of_nonneg_left (unit_pos e) hs1
      have : |x| ≤ |s • e| := by
        rw [abs_of_nonneg this]
        exact hs2
      exact I.solid this (I.smul_mem s h)

def above : Set (VectorOrderIdeal X) := { J | I.carrier ⊆ J.carrier ∧ J ≠ ⊤ }

lemma above_proper (J : above I) : e ∉ J.val := by
  by_contra hcon
  rw [← top_iff_unit_mem] at hcon
  exact J.prop.2 hcon

lemma above_contains (hI : I ≠ ⊤) : I ∈ above I := by
  constructor
  · trivial
  · exact hI

instance : Preorder (above I) where
  le_refl := by intro; trivial
  le_trans := by intro J K L hJK hKL; exact fun ⦃a⦄ a_1 ↦ hKL (hJK a_1)

def nonempty_chain_union (c : Set (above I)) (ne : c.Nonempty)
  (hc : IsChain (fun (x1 x2 : above I) => x1 ≤ x2) c) :
  VectorOrderIdeal X where
    carrier := ⋃ J ∈ c, J
    add_mem' := by
      intro x y xmem ymem
      simp only [Set.mem_iUnion] at xmem ymem ⊢
      obtain ⟨J, Jc, xJ⟩ := xmem
      obtain ⟨K, Kc, yK⟩ := ymem
      rcases hc.total Jc Kc with hJK | hKJ
      · refine ⟨K, Kc, ?_⟩
        exact K.val.add_mem' (hJK xJ) yK
      · refine ⟨J, Jc, ?_⟩
        exact J.val.add_mem' xJ (hKJ yK)
    zero_mem' := by
      simp only [Set.mem_iUnion]
      obtain ⟨J, Jc⟩ : ∃ J, J ∈ c := by
        exact ne
      refine ⟨J, Jc, J.val.zero_mem'⟩
    smul_mem' := by
      intro a x xmem
      simp only [Set.mem_iUnion] at xmem ⊢
      obtain ⟨J, Jc, xJ⟩ := xmem
      refine ⟨J, Jc, J.val.smul_mem' a xJ⟩
    supClosed' := by
      intro x xmem y ymem
      simp only [Set.mem_iUnion] at xmem ymem ⊢
      obtain ⟨J, Jc, xJ⟩ := xmem
      obtain ⟨K, Kc, yK⟩ := ymem
      rcases hc.total Jc Kc with hJK | hKJ
      · refine ⟨K, Kc, ?_⟩
        exact K.val.supClosed' (hJK xJ) yK
      · refine ⟨J, Jc, ?_⟩
        exact J.val.supClosed' xJ (hKJ yK)
    infClosed' := by
      intro x xmem y ymem
      simp only [Set.mem_iUnion] at xmem ymem ⊢
      obtain ⟨J, Jc, xJ⟩ := xmem
      obtain ⟨K, Kc, yK⟩ := ymem
      rcases hc.total Jc Kc with hJK | hKJ
      · refine ⟨K, Kc, ?_⟩
        exact K.val.infClosed' (hJK xJ) yK
      · refine ⟨J, Jc, ?_⟩
        exact J.val.infClosed' xJ (hKJ yK)
    solid := by
      intro x y hxy ymem
      simp only [Set.mem_iUnion] at ymem ⊢
      obtain ⟨J, Jc, yJ⟩ := ymem
      refine ⟨J, Jc, ?_⟩
      exact J.val.solid hxy yJ

lemma nonempty_chain_union_in_above (e : X) [IsUnitalAMSpace X e]
  (I : VectorOrderIdeal X) (c : Set (above I)) (ne : c.Nonempty)
  (hc : IsChain (fun (x1 x2 : above I) => x1 ≤ x2) c) :
    nonempty_chain_union I c ne hc ∈ above I := by
  constructor
  · intro x hx
    simp only [nonempty_chain_union, Set.mem_iUnion]
    obtain ⟨J, Jc⟩ := ne
    refine ⟨J, Jc, ?_⟩
    exact J.property.1 hx
  · by_contra hcon
    rw [top_iff_unit_mem e] at hcon
    have ⟨J, Jprop⟩ : ∃ J ∈ above I, e ∈ J := by
      change e ∈ (nonempty_chain_union I c ne hc).carrier at hcon
      simp only [nonempty_chain_union, Set.mem_iUnion] at hcon
      obtain ⟨J, Jc, eJ⟩ := hcon
      use J
      exact ⟨J.prop, eJ⟩
    exact (above_proper e I ⟨J, Jprop.1⟩) Jprop.2

lemma chain_bddabove (e : X) [IsUnitalAMSpace X e] (I : VectorOrderIdeal X)
  (hI : I ≠ ⊤) (c : Set (above I))
  (hc : IsChain (fun (x1 x2 : above I) => x1 ≤ x2) c) :
  BddAbove c := by
  by_cases ne : c.Nonempty
  · use ⟨nonempty_chain_union I c ne hc, nonempty_chain_union_in_above e I c ne hc⟩
    intro J Jc x xJ
    simp only [nonempty_chain_union, Set.mem_iUnion]
    exact ⟨J, Jc, xJ⟩
  · push_neg at ne
    use ⟨I, above_contains I hI⟩
    intro x hx
    rw [ne] at hx
    contradiction

theorem exists_le_maximal (e : X) [IsUnitalAMSpace X e] (hI : I ≠ ⊤) :
    ∃ (M : VectorOrderIdeal X), (Maximal.IsMaximal M) ∧ I ≤ M := by
    obtain ⟨M, hM⟩ :=  zorn_le (chain_bddabove e I hI)
    use M
    constructor
    · refine { out := ?_ }
      constructor
      · exact M.prop.2
      · intro J hMJ
        by_contra hcon
        push_neg at hcon
        have : I ≤ J := by
          exact le_trans M.prop.1 (le_of_lt hMJ)
        have : J ∈ above I := ⟨this, hcon⟩
        have : J = M := by
          apply le_antisymm
          · exact @hM ⟨J, this⟩ (le_of_lt hMJ)
          · exact le_of_lt hMJ
        rw [this] at hMJ
        exact lt_irrefl ↑M hMJ
    · exact M.prop.1

end UnitalAMSpace
