import NinePortIndependentSetsFitTheMatchingCapacity
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem erased_edge_at_box (i : Fin 2) {x y : X} (xin : x∈R.box i) (edge : R.erased.Adj x y) :
    x=(R.port i).tip ∧ y=(R.port i).root ∧ ¬R.essential i := by
  have outside : y∉R.box i := by
    intro yin
    have inside := R.internal_in_portPart i ((portInside_adj G (R.box i) x y).mpr ⟨edge.1,xin,yin⟩)
    have part : R.portPart i≤R.adapted := by fin_cases i;exact le_sup_left;exact le_sup_right
    exact edge.2 (part inside)
  obtain ⟨xt,yr⟩ := (R.port i).only x xin y outside edge.1
  refine ⟨xt,yr,fun he => ?_⟩
  have mem := (R.tip_reserved_iff i).mpr he
  have touch : (R.portPart i).Adj x y := ⟨edge.1,Or.inl (xt.symm ▸ mem)⟩
  have part : R.portPart i≤R.adapted := by fin_cases i;exact le_sup_left;exact le_sup_right
  exact edge.2 (part touch)

theorem erased_core_degree (x : X) (inside : x∈R.chosen) :
    Nat.card (R.erased.neighborSet x)≤1 := by
  rw [Nat.card_coe_set_eq]
  apply (Set.ncard_le_one (s:=R.erased.neighborSet x)).mpr
  intro y hy z hz
  have one (i : Fin 2) (xin : x∈R.box i) : y=z :=
    (R.erased_edge_at_box i xin hy).2.1.trans ((R.erased_edge_at_box i xin hz).2.1.symm)
  exact inside.elim (one 0) (one 1)

theorem erased_edges_off_boxes {x y : X} (hx : x∉R.chosen) (hy : y∉R.chosen) :
    R.erased.Adj x y ↔ G.Adj x y := by
  have sub : R.allReserved⊆R.chosen := Set.union_subset
    ((R.reserved_subset 0).trans Set.subset_union_left) ((R.reserved_subset 1).trans Set.subset_union_right)
  exact ⟨fun h => h.1,fun e => ⟨e,fun a => ((R.adapted_adj x y).mp a).2.elim
    (fun h => hx (sub h)) (fun h => hy (sub h))⟩⟩

theorem full_exterior_keeps_every_neighbor (cap : ∀v,Nat.card (G.neighborSet v)≤9) {x : X}
    (full : Nat.card (R.erased.neighborSet x)=9) : R.erased.neighborSet x=G.neighborSet x := by
  have sub : R.erased.neighborSet x⊆G.neighborSet x := fun _ h => h.1
  apply Set.eq_of_subset_of_ncard_le sub
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,full];exact cap x

theorem full_stage_off_boxes (B : Set X) (stage : CompleteDegreeStage R.erased 9 B) :
    Disjoint B R.chosen := by
  apply Set.disjoint_left.mpr
  intro x hx inside
  have bound := R.erased_core_degree x inside
  have actual := stage.2.1 x hx
  omega

#print axioms erased_edge_at_box
#print axioms erased_core_degree
#print axioms erased_edges_off_boxes
#print axioms full_exterior_keeps_every_neighbor
#print axioms full_stage_off_boxes
end JSP452Audit.StarHost.NinePortRegion
