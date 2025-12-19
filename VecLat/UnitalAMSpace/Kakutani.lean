import VecLat.UnitalAMSpace.Character
import VecLat.CofK

import Mathlib.Topology.ContinuousMap.StoneWeierstrass

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

lemma KT_dense_range : DenseRange (KT X e) := by
  rw [DenseRange, dense_iff_closure_eq]
  apply ContinuousMap.sublattice_closure_eq_top
  case nA =>
    use 1
    use e
    exact KT_unit_one X e
  case inf_mem =>
    intro f hf g hg
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    use x ⊓ y
    rw [← hx, ← hy]
    exact VecLatHom.map_inf' (IsVecLatHom.mk' (KT X e) (KT_veclathom X e)) x y
  case sup_mem =>
    intro f hf g hg
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    use x ⊔ y
    rw [← hx, ← hy]
    exact VecLatHom.map_sup' (IsVecLatHom.mk' (KT X e) (KT_veclathom X e)) x y
  case sep =>
    intro v φ ψ
    by_cases heq : φ = ψ
    case pos =>
      use (v φ) • 1
      constructor
      · use (v φ) • e
        rw [(KT_veclathom X e).map_smul, KT_unit_one X e]
      · constructor
        · simp
        · rw [heq]; simp
    case neg =>
      push_neg at heq
      have : ⇑φ.val ≠ ⇑ψ.val := by
        intro hval
        apply heq
        apply Subtype.ext
        exact DFunLike.coe_injective hval
      obtain ⟨x, hx⟩ := Function.ne_iff.mp this
      rw [← sub_ne_zero] at hx
      let y :=
        (φ.val x - ψ.val x)⁻¹ • ( v φ • (x - (ψ.val x) • e) +
          v ψ • ((φ.val x) • e - x))
      use KT X e y
      constructor
      · use y
      · constructor
        · change φ.val y = v φ
          unfold y
          simp [φ.prop.2]
          field_simp
        · change ψ.val y = v ψ
          unfold y
          simp [ψ.prop.2]
          field_simp

theorem Kakutani : (IsVecLatHom (KT X e)) ∧ (∀ x : X, ‖x‖=‖KT X e x‖)
∧ (DenseRange (KT X e)) ∧ (KT X e e = 1) := by
  by_cases h : e = 0
  · exact
      ⟨KT_veclathom X e, zero_KT_isometry X e h, KT_dense_range X e, KT_unit_one X e⟩
  · push_neg at h
    exact ⟨KT_veclathom X e, nonzero_KT_isometry X e h, KT_dense_range X e, KT_unit_one X e⟩
