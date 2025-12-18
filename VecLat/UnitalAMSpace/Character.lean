import VecLat.UnitalAMSpace.Maximal
import VecLat.VectorOrderIdeal.Maximal
import VecLat.VectorOrderIdeal.Quotient

import Mathlib.Topology.Algebra.Module.WeakDual

namespace UnitalAMSpace

namespace Maximal

open UnitalAMSpace PrincipalIdeal Maximal

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X] (e : X) [IsUnitalAMSpace X e]

noncomputable section

theorem exist (x : X) (h : 1 < norm e x) :
  ∃ φ : VecLatHom X ℝ, (φ e = 1) ∧ (φ |x| ≥ 1) := by
    have h' : (|x| - e)⁺ ≠ 0 := by
      by_contra hcon
      simp at hcon
      have : (1:ℝ) ∈ S e x := by
        constructor
        · norm_num
        · simp [hcon]
      apply csInf_le (S_bddbelow e x) at this
      change norm e x ≤ 1 at this
      have : _ := lt_of_le_of_lt this h
      exact (lt_self_iff_false (norm e x)).mp this
    let I : VectorOrderIdeal X := instVectorOrderIdeal (|x| - e)⁻
    have nottop : I ≠ ⊤ := by
      by_contra hcon
      have : (|x| - e)⁺ ∈ I := by rw [hcon]; trivial
      have : (|x| - e)⁺ = 0 := posPart_mem_PI_negPart (|x| - e) this
      contradiction
    obtain ⟨M, max, hIM⟩ := exists_le_maximal I e nottop
    have st_pos : 0 < Quotient.mkQ M e := by
      rw [lt_iff_le_and_ne]
      constructor
      · apply VecLatHom.monotone (Quotient.mkQ M)
        exact unit_pos e
      · by_contra hcon
        symm at hcon
        rw [Quotient.mk_eq_zero] at hcon
        rw [← top_iff_unit_mem] at hcon
        obtain ⟨hmaxcon, _⟩ := max
        contradiction
    let φ := Maximal.character M st_pos
    use φ
    constructor
    · exact Maximal.character_basis M st_pos
    · have negPart_eq_zero : φ (|x| - e)⁻ = 0 := by
        apply Maximal.character_eval M st_pos (|x| - e)⁻
        apply hIM
        exact gen_mem (|x| - e)⁻ (negPart_nonneg (|x| - e))
      have : φ |x| = φ ( (|x| - e)⁺ ) + 1 := by
        calc
          φ |x| = φ ((|x| - e)⁺ - (|x| - e)⁻ + e) := by
                  congr
                  rw [posPart_sub_negPart]
                  simp
              _ = φ ( (|x| - e)⁺ ) + φ e := by
                  rw [map_add, map_sub, negPart_eq_zero]; simp
              _ = φ ( (|x| - e)⁺ ) + 1 := by
                  rw [Maximal.character_basis M st_pos]
      calc
        φ |x| = φ (|x| - e)⁺ + 1 := by exact this
            _ ≥ 0 + 1 := by
                simp
                rw [← map_zero φ]
                apply (VecLatHom.monotone φ) (posPart_nonneg (|x| - e))
            _ = 1 := by simp

def Characters : Set (WeakDual ℝ X) := { φ | IsVecLatHom φ ∧ φ e = 1}

theorem character_contractive (φ : VecLatHom X ℝ) (h : φ e = 1) (x : X) : |φ x| ≤ norm e x := by
  calc
    |φ x| = φ |x| := by exact Eq.symm (VecLatHom.map_abs φ x)
        _ ≤ φ ((norm e x) • e) := by
          apply VecLatHom.monotone φ
          exact norm_attained e x
        _ = (norm e x) • φ e := by simp
        _ = norm e x := by simp [h]

def toStrongDual (φ : VecLatHom X ℝ) (h : φ e = 1) : StrongDual ℝ X := by
  apply LinearMap.mkContinuousOfExistsBound φ
  use 1
  intro x
  simp
  exact character_contractive e φ h x

def character_ofVecLatHom (φ : VecLatHom X ℝ) (h : φ e = 1) :
    Characters e := by
  use toStrongDual e φ h
  constructor
  · change IsVecLatHom φ
    exact VecLatHom.isVecLatHom φ
  · exact h

lemma characters_nonempty (nonzero : e ≠ 0) : (Characters e).Nonempty := by
  have : 1 < norm e ((2:ℝ) • e) := by
    rw [norm_smul e e (2:ℝ), norm_unit e nonzero]
    norm_num
  obtain ⟨φ, h1, h2⟩ := exist e ((2:ℝ) • e) this
  use toStrongDual e φ h1
  constructor
  · change IsVecLatHom φ
    exact VecLatHom.isVecLatHom φ
  · change φ e = 1
    exact h1

lemma eval_characters_nonempty (nonzero : e ≠ 0) (x : X) :
    { |φ x| | φ ∈ Characters e }.Nonempty := by
  obtain ⟨φ, h⟩ := characters_nonempty e nonzero
  use |φ x|
  simp
  use φ

lemma eval_characters_bddabove (x : X) :
    BddAbove ({ |φ x| | φ ∈ Characters e }) := by
  use norm e x
  intro t ht
  obtain ⟨φ, hφ1, hφ2⟩ := ht
  obtain ⟨h11, h12⟩ := hφ1
  rw [← hφ2]
  exact character_contractive e (VecLatHom.of_isVecLatHom φ h11) h12 x

theorem attains_norm_at_characters (nonzero : e ≠ 0) (x : X) :
    norm e x = sSup { |φ x| | φ ∈ Characters e } := by
  have norm_le_char : sSup { |φ x| | φ ∈ Characters e } ≤ norm e x := by
    refine csSup_le (eval_characters_nonempty e nonzero x) ?_
    intro t ht
    obtain ⟨φ, hφ1, hφ2⟩ := ht
    rw [← hφ2]
    obtain ⟨h, h'⟩ := hφ1
    let φ' := VecLatHom.of_isVecLatHom φ h
    exact character_contractive e φ' h' x
  cases le_or_gt (norm e x) (sSup { |φ x| | φ ∈ Characters e }) with
    | inl h =>
      apply le_antisymm
      · exact h
      · exact norm_le_char
    | inr h =>
      obtain ⟨t, ht1, ht2⟩ := exists_between h
      have : 0 ≤ sSup { |φ x| | φ ∈ Characters e } := by
        obtain ⟨s, hs⟩ := eval_characters_nonempty e nonzero x
        obtain ⟨h1, h2, h3⟩ := hs
        have : 0 ≤ s := by rw [← h3]; norm_num
        apply le_trans this
        exact le_csSup (eval_characters_bddabove e x) ⟨h1, h2, h3⟩
      have t_pos : 0 < t := Std.lt_of_le_of_lt this ht1
      have : 1 < norm e (t⁻¹ • x) := by
        rw [norm_smul]
        simp
        field_simp
        rw [abs_of_nonneg (le_of_lt t_pos)]
        exact ht2
      obtain ⟨φ, hφ1, hφ2⟩ := exist e (t⁻¹ • x) this
      rw [VecLatHom.map_abs, map_smul, abs_smul, abs_inv] at hφ2
      simp at hφ2
      field_simp at hφ2
      rw [abs_of_nonneg (le_of_lt t_pos)] at hφ2
      have : |φ x| ≤ sSup { |φ x| | φ ∈ Characters e } := by
        refine le_csSup (eval_characters_bddabove e x) ?_
        simp
        use (character_ofVecLatHom e φ hφ1)
        constructor
        · simp
        · change |φ x| = |φ x|
          simp
      apply le_trans hφ2 at this
      have : t < t := Std.lt_of_le_of_lt this ht1
      simp at this

theorem closed : IsClosed (Characters e) := by sorry

theorem compact : IsCompact (Characters e) := by sorry
  /- Use:  WeakDual.isCompact_of_bounded_of_closed -/

instance instCompactSpace : CompactSpace (Characters e) := by
  exact isCompact_iff_compactSpace.mp (compact e)

end

end Maximal

end UnitalAMSpace
