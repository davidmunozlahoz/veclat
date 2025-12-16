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

theorem attains_norm_at_Characters (x : X) :
    norm e x = sSup { |φ x| | φ ∈ Characters e } := by sorry
  /- apply le_antisymm -/
  /- · sorry -/
  /- · apply csSup_le -/
  /-   sorry -/

theorem closed : IsClosed (Characters e) := by sorry

theorem compact : IsCompact (Characters e) := by sorry
  /- Use:  WeakDual.isCompact_of_bounded_of_closed -/

instance instCompactSpace : CompactSpace (Characters e) := by
  exact isCompact_iff_compactSpace.mp (compact e)

end

end Maximal

end UnitalAMSpace
