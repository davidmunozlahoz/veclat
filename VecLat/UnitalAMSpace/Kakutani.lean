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

lemma KT_isometry (x : X) : norm e x = ‖KT X e x‖ := by
  sorry

lemma KT_unit_one : KT X e e = 1 := by
  ext ⟨φ, h1, h2⟩
  change φ e = 1
  exact h2

lemma KT_dense_range : Dense (Set.range (KT X e)) := by sorry

theorem Kakutani : (IsVecLatHom (KT X e)) ∧ (∀ x : X, ‖x‖=‖KT X e x‖) ∧ (Dense
  (Set.range (KT X e))) ∧ (KT X e e = 1) :=
  ⟨KT_veclathom X e, KT_isometry X e, KT_dense_range X e, KT_unit_one X e⟩
