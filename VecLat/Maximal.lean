import VecLat.Quotient
import VecLat.Lattice
import VecLat.UnitalAMSpace
import VecLat.VectorOrderIdeal

variable {X : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X] [Archimedean X]

namespace Maximal

variable (I : VectorOrderIdeal X)

class IsMaximal : Prop where
  out : IsCoatom I

variable [IsMaximal I]

/- instance : LinearOrder (X ⧸ I) := by sorry -/

theorem trivial_ideals (J : VectorOrderIdeal (X ⧸ I)) : (J = ⊥) ∨ (J = ⊤) := by
  /- have : I ≤ VectorOrderIdeal.comap I.mkQ J -/
  sorry

theorem arch : Archimedean (X ⧸ I) := by sorry

theorem one_dim (x y : X) (h : I.mkQ y ≠ 0) : ∃! t : ℝ,
  I.mkQ x = t • I.mkQ y := by sorry

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

omit [Archimedean X] in
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
