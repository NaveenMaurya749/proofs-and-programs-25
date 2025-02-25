  import Mathlib

  namespace lab

  -- What is this thing??
  #check outParam (Sort 9)

  /-
  class Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
  number of parameters: 2
  fields:
    Membership.mem : γ → α → Prop
  constructor:
    Membership.mk.{u, v} {α : outParam (Type u)} {γ : Type v} (mem : γ → α → Prop) : Membership α γ
  -/
  #print Membership

  inductive BinTree (α : Type) where
    | leaf (label: α) : BinTree α
    | node : BinTree α → BinTree α → BinTree α
  deriving Inhabited, Repr

  def BinTree.toList {α : Type} : BinTree α → List α
    | leaf a => [a]
    | node t₁ t₂ => toList t₁ ++ toList t₂

  /-!
  ## Membership class

  The membership typeclass represents belonging to sets, lists and other collections. The notation `x ∈ y` makes sense if `x: α`, `y: β` and there is an instance of `Membership α β`

  1. Define an instance of Membership in `BinTree α` corresponding to being a label. You may want to define an auxiliary function (or inductive type) first. (3 marks)
  -/

  -- We define an auxiliary function to help us define the instance
  def BinTree.mem {α : Type} : BinTree α → α → Prop
    | (leaf a), x => a = x
    | (node t₁ t₂), x => mem t₁ x ∨ mem t₂ x

  -- We call the auxiliary function directly by constructor Membership.mem
  instance {α : Type} : Membership α (BinTree α) :=
    ⟨BinTree.mem⟩

  /-!
  2. Prove that membership in a tree is equivalent to that in the corresponding list (3 marks).
  -/

  -- We prove the equivalence by induction on tree (matching cases on the tree constructors)
  theorem mem_tree_iff_mem_list {α : Type} (tree : BinTree α ) :
    ∀ x: α, x ∈ tree ↔ x ∈ tree.toList := by

    cases tree with
    | leaf a =>
      intro x
      simp [BinTree.toList]
      simp [Membership.mem, BinTree.mem]
      apply eq_comm

    | node t₁ t₂ =>
      intro x
      simp [BinTree.toList]

      -- We use the recursion to simplify the goal
      have h₁ : x ∈ t₁.toList ↔ x ∈ t₁ := by
        rw [mem_tree_iff_mem_list t₁]
      have h₂ : x ∈ t₂.toList ↔ x ∈ t₂ := by
        rw [mem_tree_iff_mem_list t₂]

      rw [h₁, h₂]
      simp [Membership.mem, BinTree.mem]
      -- Conclude with unfurling the definition of membership in BinTree

  /-!
  ## Decidability

  Having a decision procedure for (families of) propositions is captured by the `Decidable` typeclass. A term of `Decidable p` is either a proof that decidable is true or that it is false.
  -/

  /-
  inductive Decidable : Prop → Type
  number of parameters: 1
  constructors:
  Decidable.isFalse : {p : Prop} → ¬p → Decidable p
  Decidable.isTrue : {p : Prop} → p → Decidable p
  -/
  #print Decidable

  /-!
  3. Using that membership in a List of natural numbers is decidable (or in some other way), construct an instance of the following. Note that a convenient way to use a decidable property is with an `if` statement of the form `if c:property then ... else ...`. (3 marks)
  -/
  instance {x: Nat}{t: BinTree Nat} : Decidable (x ∈ t) := by
    -- We produce an object : Decidable (x ∈ t) by using the decidability of membership in lists
    if h : x ∈ t.toList then
      apply Decidable.isTrue
      rw [mem_tree_iff_mem_list t]
      exact h
    else
      apply Decidable.isFalse
      rw [mem_tree_iff_mem_list t]
      exact h
  /-!
  As a test, uncomment the eval statements to get the appropriate results
  -/
  open BinTree in
  def eg₁ := node (node (leaf 3) (leaf 4)) (leaf 3)

  #eval 3 ∈ eg₁

  #eval 7 ∈ eg₁

  end lab
