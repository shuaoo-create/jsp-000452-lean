import MatchEveryCoreSlotWithOnlyTheActualHallDeficitInDummySlots
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u v

def portIncidenceGraph {R:Type u} {C:Type v} (L:R→C→Prop) : SimpleGraph (R⊕C) where
  Adj x y := match x,y with
    | .inl a,.inr c => L a c
    | .inr c,.inl a => L a c
    | _,_ => False
  symm := ⟨by rintro (a|a) (b|b) e <;> exact e⟩
  loopless := ⟨by rintro (a|a) e <;> exact e⟩

namespace PortMatching
variable {R:Type u} {C:Type v} [Finite R] [Finite C] {L:R→C→Prop}
def roots (M:(portIncidenceGraph L).Subgraph) : Set R := {r|Sum.inl r∈M.verts}
def cores (M:(portIncidenceGraph L).Subgraph) : Set C := {c|Sum.inr c∈M.verts}

theorem root_has_partner {M:(portIncidenceGraph L).Subgraph} (hm:M.IsMatching) (r:roots M) :
    ∃c:cores M,M.Adj (.inl r.val) (.inr c.val) := by
  obtain ⟨x,e,_⟩ := hm r.property
  rcases x with a|c
  · exact (show False from M.adj_sub e).elim
  · exact ⟨⟨c,M.edge_vert e.symm⟩,e⟩

theorem core_has_partner {M:(portIncidenceGraph L).Subgraph} (hm:M.IsMatching) (c:cores M) :
    ∃r:roots M,M.Adj (.inl r.val) (.inr c.val) := by
  obtain ⟨x,e,_⟩ := hm c.property
  rcases x with a|b
  · exact ⟨⟨a,M.edge_vert e.symm⟩,e.symm⟩
  · exact (show False from M.adj_sub e).elim

noncomputable def mates {M:(portIncidenceGraph L).Subgraph} (hm:M.IsMatching) : ↥(cores M) ≃ ↥(roots M) where
  toFun c := (core_has_partner hm c).choose
  invFun r := (root_has_partner hm r).choose
  left_inv c := by
    apply Subtype.ext;apply Sum.inr_injective
    exact hm.eq_of_adj_left (root_has_partner hm (core_has_partner hm c).choose).choose_spec (core_has_partner hm c).choose_spec
  right_inv r := by
    apply Subtype.ext;apply Sum.inl_injective
    exact hm.eq_of_adj_left (core_has_partner hm (root_has_partner hm r).choose).choose_spec.symm (root_has_partner hm r).choose_spec.symm

theorem actual_mate_incidence {M:(portIncidenceGraph L).Subgraph} (hm:M.IsMatching) (c:cores M) :
    L (mates hm c).val c.val := M.adj_sub (core_has_partner hm c).choose_spec

theorem matched_endpoint_counts {M:(portIncidenceGraph L).Subgraph} (hm:M.IsMatching) :
    (cores M).ncard=M.edgeSet.ncard ∧ (roots M).ncard=M.edgeSet.ncard := by
  have same : (cores M).ncard=(roots M).ncard := Nat.card_congr (mates hm)
  let e : ↥(roots M)⊕↥(cores M) ≃ M.verts := {
    toFun := Sum.elim (fun a => ⟨.inl a.val,a.property⟩) (fun c => ⟨.inr c.val,c.property⟩)
    invFun := fun ⟨z,h⟩ => match z with | .inl a => .inl ⟨a,h⟩ | .inr c => .inr ⟨c,h⟩
    left_inv := by rintro (r|c) <;> rfl
    right_inv := by rintro ⟨(r|c),_⟩ <;> rfl}
  have total := Nat.card_congr e
  rw [Nat.card_sum,Nat.card_coe_set_eq,Nat.card_coe_set_eq,Nat.card_coe_set_eq] at total
  have size := matching_vertices_eq_twice_edges hm
  omega

#print axioms mates
#print axioms actual_mate_incidence
#print axioms matched_endpoint_counts
end PortMatching
end JSP452Audit.StarHost
