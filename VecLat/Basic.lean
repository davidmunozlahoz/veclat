import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic

/-
   Important files:
   - Mathlib.Algebra.Order.Group.PosPart
   - Mathlib.Algebra.Order.Group.Lattice
   - Mathlib.Algebra.Order.Group.Abs
   - Mathlib.Algebra.Order.Module.Basic
-/

class VectorLattice (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] extends
  Module ℝ X,
  PosSMulMono ℝ X

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

variable (x : X)

/- Mathlib.Algebra.Order.Module.Basic.abs_eq_zero is the same but only for -/
/- linear orders.-/

theorem abs_eq_zero_iff_zero : |x| = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← negPart_add_posPart, add_eq_zero_iff_eq_neg] at h
    have h1 : x⁺ = 0 := by
      apply le_antisymm
      · rw [← neg_zero]
        apply le_neg_of_le_neg
        rw [← h]
        exact negPart_nonneg x
      · exact posPart_nonneg x
    have h2 : x⁻ = 0 := by
      apply le_antisymm
      · rw [h]
        apply neg_le_of_neg_le
        rw [neg_zero]
        exact posPart_nonneg x
      · exact negPart_nonneg x
    rw [← posPart_sub_negPart x]
    rw [h1, h2]
    simp
  · intro h
    simp [h]

theorem uniqueness_posPart {u v : X} (hdif : x = u - v) (udisv : u ⊓ v = 0) :
    u = x⁺ := by
  symm
  calc
         x⁺ = x ⊔ 0 := by rfl
         _ = (u - v) ⊔ 0 := by rw [hdif]
         _ = u ⊔ v + (-v) := by rw [add_comm, add_sup]; simp [sub_eq_add_neg, add_comm]
         _ = u + v + (-v) := by rw [← inf_add_sup u v, udisv, zero_add]
         _ = u := by simp

theorem leq_posPart_negPart (y : X) :
    x ≤ y ↔ (x⁺ ≤ y⁺) ∧ (y⁻ ≤ x⁻) := by
    constructor
    · intro h
      constructor
      · apply sup_le_sup h (by norm_num)
      · apply sup_le_sup
        · exact neg_le_neg_iff.mpr h
        · norm_num
    · intro ⟨h1, h2⟩
      rw [← posPart_sub_negPart x, ← posPart_sub_negPart y]
      apply sub_le_sub
      · exact h1
      · exact h2

theorem Riesz_decomposition (y z : X) (xnonneg : 0 ≤ x) (ynonneg : 0 ≤ y)
  (znonneg : 0 ≤ z) (h : x ≤ y + z) : ∃ x1 x2 : X, (0 ≤ x1) ∧ (x1 ≤ y) ∧
  (0 ≤ x2) ∧ (x2 ≤ z) ∧ (x = x1 + x2) := by
    use (x ⊓ y); use (x - x ⊓ y)
    repeat (any_goals constructor)
    · exact le_inf xnonneg ynonneg
    · exact inf_le_right
    · simp
    · rw [sub_inf]
      have : x - y ≤ z := by
        calc
          x - y = x + (-y) := by rw [sub_eq_add_neg]
              _ ≤ (y + z) + (-y) := by apply add_le_add h (le_refl (-y))
              _ ≤ z := by simp
      rw [leq_posPart_negPart] at this
      rw [sub_self, sup_comm, ← posPart_def]
      rw [← posPart_of_nonneg znonneg]
      exact this.1
    · simp

end LatticeOrderedGroup

section VectorLattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

variable (x y : X)

theorem nonneg_smul_sup (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by
  by_cases h : a = 0
  · subst h
    simp only [zero_smul]; exact Eq.symm Std.max_self
  · apply le_antisymm
    · have hx : a⁻¹ • a • x ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_left
         (by norm_num [nonneg])
      have hy : a⁻¹ • a • y ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_right
         (by norm_num [nonneg])
      simp [h] at hx hy
      have hxy : x ⊔ y ≤ a⁻¹ • (a • x ⊔ a • y) :=
        sup_le hx hy
      calc
        a • (x ⊔ y) ≤ a • (a⁻¹ • (a • x ⊔ a • y)) := by
                      exact smul_le_smul_of_nonneg_left hxy nonneg
                  _ = a • x ⊔ a • y := by rw [smul_smul a a⁻¹ _]; norm_num [h];
    · have hx : a • x ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_left nonneg
      have hy : a • y ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_right nonneg
      exact sup_le hx hy

theorem nonneg_smul_inf (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by
    calc
      a • (x ⊓ y) = (-1) • a • (- (x ⊓ y)) := by simp
                _ = (-1) • a • ((-x) ⊔ (-y)) := by rw [neg_inf]
                _ = (-1) • ((a • -x) ⊔ (a • -y)) := by rw [nonneg_smul_sup (-x) (-y) a nonneg]
                _ = - ((-a • x) ⊔ (-a • y)) := by simp
                _ = (a • x) ⊓ (a • y) := by rw [neg_sup]; simp

theorem sup_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊔ b) • x = (a • x) ⊔ (b • x) := by
  apply le_antisymm
  · cases max_choice a b with
      | inl h => rw [h]; exact le_sup_left
      | inr h => rw [h]; exact le_sup_right
  · apply sup_le
    · exact smul_le_smul_of_nonneg_right le_sup_left h
    · exact smul_le_smul_of_nonneg_right le_sup_right h

theorem inf_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊓ b) • x = (a • x) ⊓ (b • x) := by
  apply le_antisymm
  · apply le_inf
    · exact smul_le_smul_of_nonneg_right inf_le_left h
    · exact smul_le_smul_of_nonneg_right inf_le_right h
  · cases min_choice a b with
      | inl h => rw [h]; exact inf_le_left
      | inr h => rw [h]; exact inf_le_right

/- Already in mathlib but only for total orders. -/

theorem abs_smul' (a : ℝ) : |a • x| = |a| • |x| := by
  by_cases ha : a ≥ 0
  · rw [abs_of_nonneg ha]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) a ha]
    simp
  · have hna : a < 0 := by linarith
    rw [abs_of_neg hna]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) (-a) (by linarith)]
    simp [sup_comm]

theorem disjoint_smul (a : ℝ) (nonneg : 0 ≤ a) (h : x ⊓ y = 0) :
    (a • x) ⊓ y = 0 := by
  let aux (x y : X) (h : x ⊓ y = 0) (a : ℝ)
  (nonneg : 0 ≤ a) (hone : a ≤ 1) : (a • x) ⊓ y = 0 := by
    have xnonneg : 0 ≤ x := by rw [← h]; exact inf_le_left
    have ynonneg : 0 ≤ y := by rw [← h]; exact inf_le_right
    apply le_antisymm
    · calc
        a • x ⊓ y ≤ (1 : ℝ) • x ⊓ y := by
            apply inf_le_inf
            · exact smul_le_smul_of_nonneg_right hone xnonneg
            · exact le_refl y
          _ = 0 := by simp [h]
    · apply le_inf
      · exact smul_nonneg nonneg xnonneg
      · exact ynonneg
  have (hone : ¬ a ≤ 1) : (a • x) ⊓ y = 0 := by
    push_neg at hone
    suffices x ⊓ (a⁻¹ • y) = 0 from by
      symm
      calc
        0 = a • ( x ⊓ (a⁻¹ • y) ):= by rw [this, smul_zero]
        _ = (a • x ⊓ a • a⁻¹ • y) := by
            exact nonneg_smul_inf x (a⁻¹ • y) a nonneg
        _ = (a • x) ⊓ y := by rw [smul_smul]; field_simp [hone]; simp
    rw [inf_comm]
    rw [inf_comm] at h
    refine aux y x h a⁻¹ ?nonneg ?one
    · exact inv_nonneg.mpr nonneg
    · field_simp
      exact (le_of_lt hone)
  by_cases hone : a ≤ 1
  · exact aux x y h a nonneg hone
  · exact this hone

section Archimedean

variable [Archimedean X]

omit [VectorLattice X] in
lemma infinitesimal_is_zero {x y : X}
  (infinitesimal : ∀ n : ℕ, n • |x| ≤ y) : x = 0 := by
  by_contra h
  have : 0 < |x| := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro heq
    symm at heq
    have : x = 0 := by apply (abs_eq_zero_iff_zero x).mp heq
    contradiction
  obtain ⟨n, hn⟩ := exists_lt_nsmul this y
  specialize infinitesimal n
  have : n • |x| < n • |x| := by
    apply lt_of_le_of_lt infinitesimal hn
  apply lt_irrefl (n • |x|) this

theorem arch' {x y : X} (h : ∀ n : ℕ, n • x ≤ y) : x ≤ 0 := by
  apply (leq_posPart_negPart x 0).mpr
  constructor
  · have : ∀ n : ℕ, n • |x⁺| ≤ y⁺ := by
      intro n
      calc
        n • |x⁺| = n • x⁺ := by congr; apply abs_of_nonneg (posPart_nonneg x)
               _ = n • (x ⊔ 0) := by rw [posPart_def]
               _ = (n:ℝ) • (x ⊔ 0) := by norm_cast
               _ = ((n:ℝ) • x) ⊔ ((n:ℝ) • 0) := by
                 rw [nonneg_smul_sup x 0 (n:ℝ) (by norm_num)]
               _ = ((n:ℝ) • x) ⊔ 0 := by rw [smul_zero (n:ℝ)]
               _ = ((n:ℝ) • x)⁺ := by rw [posPart_def]
               _ ≤ y⁺ := by norm_cast; exact ((leq_posPart_negPart (n • x) y).mp (h n)).1
    have xpos_zero : x⁺ = 0 := infinitesimal_is_zero this
    rw [xpos_zero]
    simp
  · simp
    exact negPart_nonneg x

end Archimedean

noncomputable instance : VectorLattice ℝ := {
  toModule := inferInstance
  toPosSMulMono := inferInstance
}

end VectorLattice
