import VecLat.VectorOrderIdeal.Basic

variable {X : Type*} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

namespace VectorOrderIdeal

instance : Bot (VectorOrderIdeal X) :=
  ⟨{ (⊥ : Submodule ℝ X) with
      supClosed' := by
        intro x xmem y ymem
        simp at xmem ymem; simp [xmem, ymem]
      infClosed' := by
        intro x xmem y ymem
        simp at xmem ymem; simp [xmem, ymem]
      solid := by
        intro x y hxy ymem
        simp at ymem; simp
        rw [← abs_eq_zero_iff_zero]
        apply le_antisymm
        · apply le_trans hxy
          simp [ymem]
        · exact abs_nonneg x
  }⟩

theorem bot_carrier : (⊥ : VectorOrderIdeal X).carrier = {0} :=
  rfl

theorem mem_bot {x : X} : x ∈ (⊥ : VectorOrderIdeal X) ↔ x = 0 :=
  Set.mem_singleton_iff

instance : Top (VectorOrderIdeal X) :=
  ⟨{ (⊤ : Submodule ℝ X) with
      supClosed' := by
        intro x xmem y ymem
        simp
      infClosed' := by
        intro x xmem y ymem
        simp
      solid := by
        intro x y hxy ymem
        simp
  }⟩

theorem top_coe : ((⊤ : VectorOrderIdeal X) : Set X) = Set.univ :=
  rfl

instance : LE (VectorOrderIdeal X) :=
  {
    le := fun I J => I.carrier ⊆ J.carrier
  }

instance : BoundedOrder (VectorOrderIdeal X) :=
  {
    le_top := by
      intro I x xmem
      trivial
    bot_le := by
      intro I x xmem
      rw [bot_carrier] at xmem
      simp at xmem
      rw [xmem]
      simp
  }

end VectorOrderIdeal
