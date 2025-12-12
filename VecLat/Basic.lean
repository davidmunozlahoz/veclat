import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic

set_option linter.unusedSectionVars false

class VectorLattice (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] extends
  Module ℝ X,
  PosSMulMono ℝ X

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]

@[simp]
def posp (x : X) := x ⊔ 0

@[simp]
def negp (x : X) := (-x) ⊔ 0

notation x "₊" => posp x
notation x "₋" => negp x

lemma posp_nonneg (x : X) : x₊ ≥ 0 := by
  rw [posp]
  exact le_sup_right

lemma nonneg_eq_posp {x : X} (h : 0 ≤ x) : posp x = x := by
  dsimp
  exact sup_eq_left.mpr h

lemma negp_nonneg (x : X) : negp x ≥ 0 := by simp

lemma nonneg_smul_sup (x y : X) (a : ℝ) (apos : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by
  by_cases h : a = 0
  · subst h
    simp only [zero_smul]; exact Eq.symm Std.max_self
  · apply le_antisymm
    · have hx : a⁻¹ • a • x ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_left
         (by norm_num [apos])
      have hy : a⁻¹ • a • y ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_right
         (by norm_num [apos])
      simp [h] at hx hy
      have hxy : x ⊔ y ≤ a⁻¹ • (a • x ⊔ a • y) :=
        sup_le hx hy
      calc
        a • (x ⊔ y) ≤ a • (a⁻¹ • (a • x ⊔ a • y)) := by exact smul_le_smul_of_nonneg_left hxy apos
                  _ = a • x ⊔ a • y := by rw [smul_smul a a⁻¹ _]; norm_num [h];
    · have hx : a • x ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_left apos
      have hy : a • y ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_right apos
      exact sup_le hx hy

lemma nonneg_smul_inf (x y : X) (a : ℝ) (apos : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by
    calc
      a • (x ⊓ y) = (-1) • a • (- (x ⊓ y)) := by simp
                _ = (-1) • a • ((-x) ⊔ (-y)) := by rw [neg_inf]
                _ = (-1) • ((a • -x) ⊔ (a • -y)) := by rw [nonneg_smul_sup (-x) (-y) a apos]
                _ = - ((-a • x) ⊔ (-a • y)) := by simp
                _ = (a • x) ⊓ (a • y) := by rw [neg_sup]; simp


lemma posp_sub_negp (x : X) : x = posp x - negp x := by
  dsimp
  rw [sub_eq_add_neg, neg_sup, neg_neg, add_comm]
  simp
  rw [inf_add_sup]
  simp

lemma posp_add_negp (x : X) : abs x = posp x + negp x := by
  symm
  calc
    posp x + negp x = posp x + posp x - (posp x - negp x) := by abel_nf
                  _ = (1:ℝ) • posp x + (1:ℝ) • posp x - (posp x - negp x) := by rw [one_smul]
                  _ = (1 + 1 : ℝ) • posp x - (posp x - negp x) := by rw
                      [← add_smul (1:ℝ) (1:ℝ) (posp x)]
                  _ = (2 : ℝ) • posp x - x := by rw [← posp_sub_negp]; norm_num
                  _ = (2 : ℝ) • (x ⊔ 0) - x := by dsimp
                  _ = ((2:ℝ) • x) ⊔ ((2:ℝ) • 0) - x := by rw
                      [nonneg_smul_sup x 0 (2:ℝ) (by norm_num)]
                  _ = (-x + (2:ℝ) • x) ⊔ (-x) := by rw [sub_eq_add_neg, add_comm,add_sup]; simp
                  _ = (-((1:ℝ) • x) + (2:ℝ) • x) ⊔ (-x) := by rw [one_smul]
                  _ = ( (-1:ℝ) • x + (2:ℝ) • x) ⊔ (-x) := by rw [neg_smul]
                  _ = ( (-1+2:ℝ) • x ) ⊔ (-x) := by rw [← add_smul]
                  _ = ( 1 • x) ⊔ (-x) := by norm_num
                  _ = x ⊔ (-x) := by rw [one_smul]
                  _ = abs x := by rfl

lemma leq_posp_negp {x y : X} : x ≤ y ↔
  (posp x ≤ posp y) ∧ (negp y ≤ negp x) := by
    constructor
    · intro h
      constructor
      · apply sup_le_sup h (by norm_num)
      · apply sup_le_sup
        · exact neg_le_neg_iff.mpr h
        · norm_num
    · intro ⟨h1, h2⟩
      rw [posp_sub_negp x, posp_sub_negp y]
      apply sub_le_sub
      · exact h1
      · exact h2

lemma sup_of_dis_eq_sum {x y : X} (dis : x ⊓ y = 0) : x + y = x ⊔ y := by
  rw [← inf_add_sup, dis]; simp

lemma uniqueness_posp {x u v : X} (hdif : x = u - v) (udisv : u ⊓ v = 0) : u = posp x := by
  symm
  calc
    posp x = x ⊔ 0 := by rfl
         _ = (u - v) ⊔ 0 := by rw [hdif]
         _ = u ⊔ v + (-v) := by rw [add_comm, add_sup]; simp [sub_eq_add_neg, add_comm]
         _ = u + v + (-v) := by rw [← sup_of_dis_eq_sum udisv]
         _ = u := by simp

attribute [simp] abs

/- Mathlib.Algebra.Order.Module.Basic.abs_smul is the same but only for -/
/- linear orders. I don't know if using a prime is the proper solution.-/

/- #check abs_eq_zero -/
/- #check abs_smul -/
/- #check abs_add_le -/

lemma abs_eq_zero_iff_zero {x : X} : abs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [posp_add_negp] at h
    have aux1 : posp x = - negp x := by
      calc
        posp x = posp x + negp x + (- negp x) := by rw [add_neg_cancel_right]
              _ = 0 + (- negp x) := by rw [h]
              _ = - negp x := by simp
    have h1 : posp x = 0 := by
      apply le_antisymm
      · rw [aux1]; apply neg_le.mp; simp
      · exact posp_nonneg x
    have aux2 : negp x = - posp x := by
      calc
        negp x = posp x + negp x + (- posp x) := by simp
              _ = 0 + (- posp x) := by rw [h]
              _ = - posp x := by simp
    have h2 : negp x = 0 := by
      apply le_antisymm
      · rw [aux2]; apply neg_le.mp; simp
      · exact negp_nonneg x
    rw [posp_sub_negp x]
    rw [h1, h2]
    simp
  · intro h
    simp [h]

lemma abs_smul' {x : X} {a : ℝ} : |a • x| = |a| • |x| := by
  by_cases ha : a ≥ 0
  · rw [abs_of_nonneg ha]
    simp
    rw [nonneg_smul_sup x (-x) a ha]
    simp
  · have hna : a < 0 := by linarith
    rw [abs_of_neg hna]
    dsimp
    rw [nonneg_smul_sup x (-x) (-a) (by linarith)]
    simp [sup_comm]

lemma disjoint_smul (x y : X) (a : ℝ) (ha : 0 ≤ a) (h : x ⊓ y = 0) :
    (a • x) ⊓ y = 0 := by
  have xnonneg : 0 ≤ x := by rw [← h]; exact inf_le_left
  have ynonneg : 0 ≤ y := by rw [← h]; exact inf_le_right
  by_cases hone : 1 ≤ a
  · sorry
  · push_neg at hone
    apply le_antisymm
    · calc
        a • x ⊓ y ≤ (1 : ℝ) • x ⊓ y := by
            apply inf_le_inf
            · exact smul_le_smul_of_nonneg_right (le_of_lt hone) xnonneg
            · exact le_refl y
          _ = 0 := by simp [h]
    · apply le_inf
      · exact smul_nonneg ha xnonneg
      · exact ynonneg


lemma sub_inf_posp_sub (x y : X) : x - x ⊓ y = posp (x-y) := by
  calc
    x - x ⊓ y = x + (-x) ⊔ (-y) := by rw [sub_eq_add_neg, neg_inf]
            _ = 0 ⊔ (x-y) := by rw [add_sup]; simp [sub_eq_add_neg]
            _ = posp (x-y) := by simp; rw [sup_comm]

lemma sup_sub_posp_sub (x y : X) : x ⊔ y - x = posp (y-x) := by
  calc
    x ⊔ y - x = (x - x) ⊔ (y - x) := by rw [sup_sub x y x]
            _ = 0 ⊔ (y - x) := by simp
            _ = posp (y - x) := by simp; exact sup_comm 0 (y - x)

lemma posp_sub_eq_zero_iff {x y : X} : posp (x-y) = 0 ↔ x ≤ y := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp [h]

lemma negp_sub_eq_zero_iff {x y : X} : negp (x-y) = 0 ↔ y ≤ x := by
  constructor
  · intro h
    simp at h
    exact h
  · intro h
    simp [h]

theorem Riesz_decomposition {x y z : X} (xpos : 0 ≤ x) (ypos : 0 ≤ y)
  (zpos : 0 ≤ z) (h : x ≤ y + z) : ∃ x1 x2 : X, (0 ≤ x1) ∧ (x1 ≤ y) ∧
  (0 ≤ x2) ∧ (x2 ≤ z) ∧ (x = x1 + x2) := by
    use (x ⊓ y); use (x - x ⊓ y)
    repeat (any_goals constructor)
    · exact le_inf xpos ypos
    · exact inf_le_right
    · simp
    · rw [sub_inf_posp_sub]
      have : x - y ≤ z := by
        calc
          x - y = x + (-y) := by rw [sub_eq_add_neg]
              _ ≤ (y + z) + (-y) := by apply add_le_add h (le_refl (-y))
              _ ≤ z := by simp
      rw [leq_posp_negp] at this
      rw [← nonneg_eq_posp zpos]
      exact this.1
    · simp

variable [Archimedean X]

lemma infinitesimal_is_zero {x y : X}
  (infinitesimal : ∀ n : ℕ, n • |x| ≤ y) : x = 0 := by
  by_contra h
  have : 0 < |x| := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro heq
    symm at heq
    have : x = 0 := by apply abs_eq_zero_iff_zero.mp heq
    contradiction
  obtain ⟨n, hn⟩ := exists_lt_nsmul this y
  specialize infinitesimal n
  have : n • |x| < n • |x| := by
    apply lt_of_le_of_lt infinitesimal hn
  apply lt_irrefl (n • |x|) this

lemma arch' {x y : X} (h : ∀ n : ℕ, n • x ≤ y) : x ≤ 0 := by
  apply leq_posp_negp.mpr
  constructor
  · have : ∀ n : ℕ, n • |x₊| ≤ y₊ := by
      intro n
      calc
        n • |x₊| = n • x₊ := by congr; apply abs_of_nonneg (posp_nonneg x)
               _ = n • (x ⊔ 0) := by simp
               _ = (n:ℝ) • (x ⊔ 0) := by exact Eq.symm (Nat.cast_smul_eq_nsmul ℝ n (x ⊔ 0))
               _ = ((n:ℝ) • x) ⊔ ((n:ℝ) • 0) := by rw [nonneg_smul_sup x 0 (n:ℝ) (by norm_num)]
               _ = ((n:ℝ) • x ) ⊔ 0 := by simp
               _ = ((n:ℝ) • x)₊ := by simp
               _ = (n • x)₊ := by rw [Nat.cast_smul_eq_nsmul ℝ n x]
               _ ≤ y₊ := by exact (leq_posp_negp.mp (h n)).1
    have xpos_zero : x₊ = 0 := infinitesimal_is_zero this
    rw [xpos_zero]
    simp
  · simp

noncomputable instance : VectorLattice ℝ := {
  toModule := inferInstance
  toPosSMulMono := inferInstance
}
