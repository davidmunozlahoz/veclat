import VecLat.UnitalAMSpace.Character
import VecLat.CofK

open UnitalAMSpace Maximal

variable (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
[VectorLattice X] [Archimedean X] (e : X) [IsUnitalAMSpace X e]

def KT (x : X) : C(Characters e, ℝ) where
  toFun := fun φ => (φ : X → ℝ) x
  continuous_toFun := by
    have : Continuous (fun (φ : WeakDual ℝ X) => (φ : X → ℝ) x) := by
      exact WeakDual.eval_continuous x
    change Continuous ((Characters e).restrict (fun (φ : WeakDual ℝ X) => (φ : X → ℝ) x))
    rw [← continuousOn_iff_continuous_restrict]
    exact this.continuousOn

lemma KT_veclathom : IsVecLatHom (KT X e) where
  map_add := by
    intro x y
    ext ⟨φ, h1, h2⟩
    change φ (x + y) = φ x + φ y
    exact h1.map_add x y
  map_smul := by
    intro c x
    ext ⟨φ, h1, h2⟩
    change φ (c • x) = c • φ x
    exact h1.map_smul c x
  map_sup' := by
    intro x y
    ext ⟨φ, h1, h2⟩
    change φ (x ⊔ y) = φ x ⊔ φ y
    exact h1.map_sup' x y
  map_inf' := by
    intro x y
    ext ⟨φ, h1, h2⟩
    change φ (x ⊓ y) = φ x ⊓ φ y
    exact h1.map_inf' x y

lemma nonzero_KT_isometry (nonzero : e ≠ 0) (x : X) : norm e x = ‖KT X e x‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, KT]
  change norm e x = sSup { |φ.1 x| | φ : Characters e }
  convert (attains_norm_at_characters e nonzero x)
  constructor
  · intro ⟨φ, hφ⟩
    use φ
    simp [hφ]
  · intro ⟨φ, hφ⟩
    use ⟨φ, hφ.1⟩
    simp [hφ]

lemma zero_KT_isometry (hzero : e = 0) (x : X) : norm e x = ‖KT X e x‖ := by
  have hzero (y : X) : y = 0 := by
    obtain ⟨s, hs1, hs2⟩ := unit_def e y
    rw [hzero] at hs2
    simp at hs2
    rw [← abs_eq_zero_iff_zero]
    exact le_antisymm hs2 (abs_nonneg y)
  rw [(norm_zero_iff_zero e x).mpr (hzero x), hzero x]
  have : KT X e = 0 := by
    ext y φ
    dsimp [KT]
    rw [hzero y]
    simp
  rw [this]
  simp

lemma KT_unit_one : KT X e e = 1 := by
  ext ⟨φ, h1, h2⟩
  change φ e = 1
  exact h2

lemma KT_dense_range : Dense (Set.range (KT X e)) := by sorry

theorem Kakutani : (IsVecLatHom (KT X e)) ∧ (∀ x : X, ‖x‖=‖KT X e x‖) ∧ (Dense
  (Set.range (KT X e))) ∧ (KT X e e = 1) := by
  by_cases h : e = 0
  · exact
      ⟨KT_veclathom X e, zero_KT_isometry X e h, KT_dense_range X e, KT_unit_one X e⟩
  · push_neg at h
    exact ⟨KT_veclathom X e, nonzero_KT_isometry X e h, KT_dense_range X e, KT_unit_one X e⟩
