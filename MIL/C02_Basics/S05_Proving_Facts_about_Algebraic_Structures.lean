import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α] -- this describes a type which supports partial ordering
variable (x y z : α)  -- this describes x, y, z as variables of the type alpha

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  · apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    apply le_trans
    apply inf_le_left
    apply inf_le_left
    apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_right
    · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply le_trans
        apply inf_le_left
        apply le_refl
      · apply le_trans
        apply inf_le_right
        apply inf_le_left
    · apply le_trans
      apply inf_le_right
      apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
  · apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    apply sup_le
    · apply le_sup_left
    · apply le_trans (b := y ⊔ z)
      apply le_sup_left
      apply le_sup_right
    · apply le_trans (b := y ⊔ z)
      apply le_sup_right
      apply le_sup_right
  · apply sup_le
    · apply le_trans (b := x ⊔ y)
      apply le_sup_left
      apply le_sup_left
    · apply sup_le
      · apply le_trans (b := x ⊔ y)
        apply le_sup_right
        apply le_sup_left
      · apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    apply le_refl
    apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw[inf_comm (a := a ⊔ b) (b := a)]
  rw[absorb1]
  rw[inf_comm (a := a ⊔ b)]
  rw[h]
  rw[← sup_assoc]
  rw[inf_comm (a := c)]
  rw[absorb2]
  rw[inf_comm (a:=c)]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (b := a)]
  rw[absorb2]
  rw [sup_comm (a := a ⊓ b)]
  rw [h]
  rw [← inf_assoc]
  rw [sup_comm (a := c)]
  rw [absorb1]
  rw [sup_comm (a := b)]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_right
  exact h

theorem aux2 (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_right
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1: 0 ≤ b - a := by
    apply aux1 a b
    exact h
  have h2 : 0 ≤ (b - a) * c := by
    exact mul_nonneg h1 h'
  apply aux2
  rw [← sub_mul]
  exact h2

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h: 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  rw [dist_comm y x] at h
  linarith

end
