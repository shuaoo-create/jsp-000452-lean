import DegreePotential
import StarMatchingColor
import StarMatchingCharge

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A maximum matching used as red edges prevents every red star of size ≥2. -/
theorem matching_blue_potential {X : Type*} [Finite X] (G : SimpleGraph X) {a b : ℕ}
    (ha : 2≤a) (forced : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, b + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  obtain ⟨M,matchM,maxM⟩ := exists_maximum_matching G
  obtain ⟨v,budget⟩ := blue_center_of_matching_coloring M matchM ha forced
  exact ⟨v,paid_potential_of_counts G v b (blue_matching_charge G M matchM maxM v b budget)⟩

private theorem small_left {X : Type*} [Finite X] (G : SimpleGraph X) {a b : ℕ}
    (ha : 0<a) (small : a≤2) (forced : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, (a+b-2) + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  by_cases two : 2≤a
  · obtain ⟨v,h⟩ := matching_blue_potential G two forced
    exact ⟨v,by omega⟩
  · obtain ⟨v,deg⟩ := high_degree_of_blue G ha forced
    have h := degree_potential_charge G v
    exact ⟨v,by omega⟩

/-- The exact single-star potential lemma (Liu lines 258–270) for the nontrivial
    family in which at least one star has one or two leaves. -/
theorem local_potential_small {X : Type*} [Finite X] (G : SimpleGraph X) {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (small : a≤2 ∨ b≤2) (forced : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, (a+b-2) + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  cases small with
  | inl h => exact small_left G ha h forced
  | inr h => simpa only [Nat.add_comm b a] using small_left G hb h (forces_swap forced)

#print axioms local_potential_small
end JSP452Audit.StarHost
