
  theorem trees_non_empty {α : Type} : (t : BinTree α) → 0 < t.toList.length := by
    intro t
    cases t with
    | leaf a =>
      simp [BinTree.toList]
    | node t₁ t₂ =>
      simp [BinTree.toList]
      left
      exact trees_non_empty t₁

  theorem subtree_lt_tree {α : Type} : (sub : BinTree α) → (tree : BinTree α)
   → (h : ∃ (other : BinTree α), tree = sub.node other ∨ tree = other.node sub)
   → sub.toList.length < tree.toList.length := by
    intro sub tree h
    let ⟨other, proof⟩ := h
    have h₀ : sub.toList.length < sub.toList.length + other.toList.length := by
      apply Nat.lt_add_of_pos_right
      exact trees_non_empty other
    have h₁ : sub.toList.length + other.toList.length = tree.toList.length := by
      cases proof with
      | inl p =>
        rw [p]
        simp [BinTree.toList]
      | inr p =>
        rw [p]
        simp [BinTree.toList, add_comm]
    rw [h₁] at h₀
    exact h₀
