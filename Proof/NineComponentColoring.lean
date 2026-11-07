import NineTripleDomination
import ExactPathEvenSplit
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Keep all edges outside the centers red. Each full-degree vertex outside
the centers loses a neighbor, and every blue edge meets the centers. -/
theorem coloring_from_centers (G : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (S : Set X)
    (hits : ∀x,Nat.card (G.neighborSet x)=D → x∉S → ∃y∈S,G.Adj x y) :
    ∃ R : SimpleGraph X,R≤G ∧ (∀x,Nat.card (R.neighborSet x)≤D-1) ∧
      matchingEdges (G \ R) ≤ S.ncard := by
  classical
  let R : SimpleGraph X := {
    Adj a b := G.Adj a b ∧ a∉S ∧ b∉S
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  have sub : R≤G := fun _ _ h => h.1
  refine ⟨R,sub,?_,matchingEdges_le_cover_card _ S ?_⟩
  · intro x
    rw [Nat.card_coe_set_eq]
    have small : R.neighborSet x⊆G.neighborSet x := fun _ h => sub h
    have bound := cap x
    rw [Nat.card_coe_set_eq] at bound
    by_cases full : (G.neighborSet x).ncard=D
    · by_cases inS : x∈S
      · have empty : R.neighborSet x=∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun _ h => (show _ ∧ x∉S ∧ _ from h).2.1 inS)
        rw [empty,Set.ncard_empty];omega
      · obtain ⟨y,hy,adj⟩ := hits x (by rwa [Nat.card_coe_set_eq]) inS
        have diff := Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr
          ⟨small,y,adj,fun (h : R.Adj x y) => h.2.2 hy⟩)
        omega
    · have bound' := Set.ncard_le_ncard small
      omega
  · intro x y h
    by_contra! away
    exact h.2 ⟨h.1,away.1,away.2⟩

/-- The same two-color obstruction holds on the original graph with any
number of isolated labels outside the nine-vertex component. -/
theorem nine_component_coloring (G : SimpleGraph X) (c : G.ConnectedComponent)
    (order : Nat.card c.supp=9)
    (reg : ∀v:c.supp,Nat.card (c.toSimpleGraph.neighborSet v)=4)
    (only : ∀ ⦃x y⦄,G.Adj x y → x∈c.supp) :
    ∃R : SimpleGraph X,R≤G ∧ (∀x,Nat.card (R.neighborSet x)≤3) ∧ matchingEdges (G \ R)≤3 := by
  obtain ⟨T,three,dom⟩ := four_regular_nine_dominating_three c.toSimpleGraph order reg
  let S : Set X := Subtype.val '' T
  have sc : S.ncard≤3 := (Set.ncard_image_of_injective T Subtype.val_injective).le.trans three
  have outside (x : X) (hx : x∉c.supp) : Nat.card (G.neighborSet x)=0 := by
    have emp : G.neighborSet x=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun y edge => hx (only edge))
    rw [Nat.card_coe_set_eq,emp,Set.ncard_empty]
  have cap (x : X) : Nat.card (G.neighborSet x)≤4 := by
    by_cases hx : x∈c.supp
    · let v : c.supp := ⟨x,hx⟩
      exact ((component_degree_eq G c v).symm.trans (reg v)).le
    · rw [outside x hx];omega
  have hits (x : X) (full : Nat.card (G.neighborSet x)=4) (xs : x∉S) : ∃y∈S,G.Adj x y := by
    have inside : x∈c.supp := by
      by_contra hx
      have z := outside x hx
      omega
    let v : c.supp := ⟨x,inside⟩
    obtain ⟨u,ut,edge⟩ := dom v (fun h => xs ⟨v,h,rfl⟩)
    exact ⟨u.val,⟨u,ut,rfl⟩,edge⟩
  obtain ⟨R,sub,rd,blue⟩ := coloring_from_centers G 4 (by decide) cap S hits
  exact ⟨R,sub,rd,blue.trans sc⟩

#print axioms coloring_from_centers
#print axioms nine_component_coloring
end JSP452Audit.StarHost
