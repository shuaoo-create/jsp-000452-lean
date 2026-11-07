import ThePortCutsSplitTheActualResidualIntoItsTwoInducedGraphs
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)

theorem spent_count (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) :
    (W.spent I V).ncard=W.innerTips.ncard+I.ncard+V.ncard := by
  have d₁ : Disjoint W.innerTips (W.liftInside I) := Set.disjoint_left.mpr (by
    rintro x hx ⟨v,_,rfl⟩;exact v.property.2 hx)
  have inside : W.innerCut I⊆W.support := by
    rintro x (z|⟨v,_,rfl⟩);exact z.1;exact v.property.1
  have d₂ : Disjoint (W.innerCut I) (Subtype.val '' V) := Set.disjoint_left.mpr (by
    rintro x hx ⟨v,_,rfl⟩;exact v.property (inside hx))
  rw [spent,Set.ncard_union_eq d₂,innerCut,Set.ncard_union_eq d₁,liftInside,
    Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_image_of_injective _ Subtype.val_injective]

theorem spent_edges (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) :
    (G.induce (W.spent I V)ᶜ).edgeSet.ncard=
        ((G.induce W.available).induce Iᶜ).edgeSet.ncard+(W.outside.induce Vᶜ).edgeSet.ncard := by
  have e : (((G.induce W.available).induce Iᶜ)⊕g W.outside.induce Vᶜ).edgeSet.ncard=
    (G.induce (W.spent I V)ᶜ).edgeSet.ncard := Nat.card_congr (W.after_port_cuts I V).mapEdgeSet
  rw [edge_ncard_sumGraph] at e;exact e.symm

theorem spent_cap (I:Set W.available) (V:Set ↥(W.supportᶜ:Set X)) (D:ℕ)
    (left:∀v,Nat.card (((G.induce W.available).induce Iᶜ).neighborSet v)≤D)
    (right:∀v,Nat.card ((W.outside.induce Vᶜ).neighborSet v)≤D) :
    ∀v,Nat.card ((G.induce (W.spent I V)ᶜ).neighborSet v)≤D := by
  let e := W.after_port_cuts I V
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  rw [←Nat.card_congr (e.mapNeighborSet x)]
  rcases x with x|x
  · rw [neighborSet_sum_inl,Nat.card_coe_set_eq,Set.ncard_image_of_injective _ Sum.inl_injective];exact left x
  · rw [neighborSet_sum_inr,Nat.card_coe_set_eq,Set.ncard_image_of_injective _ Sum.inr_injective];exact right x

theorem seed_edge_split (cap:∀x,Nat.card (G.neighborSet x)≤10) :
    G.edgeSet.ncard+W.seedLoss=(G.induce W.available).edgeSet.ncard+W.outside.edgeSet.ncard+10*W.innerTips.ncard := by
  have covers : W.available∪W.supportᶜ=W.innerTipsᶜ := by
    ext x
    change ((x∈W.support ∧ x∉W.innerTips) ∨ x∉W.support) ↔ x∉W.innerTips
    have sub : x∈W.innerTips → x∈W.support := fun m => m.1
    tauto
  let iso := regionSumIso G W.innerTipsᶜ W.available W.supportᶜ covers
    (disjoint_compl_right.mono_left Set.sdiff_subset)
    (fun x hx _ hy e => hy (W.ordinary_neighbors_stay hx.1 hx.2 e))
  have base : ((G.induce W.available)⊕g W.outside).edgeSet.ncard=(G.induce W.innerTipsᶜ).edgeSet.ncard := Nat.card_congr iso.mapEdgeSet
  rw [edge_ncard_sumGraph] at base
  have price := root_deletion_cost_with_slack G W.innerTips 10 (fun v _ => cap v)
  change G.edgeSet.ncard+rootShortfall G W.innerTips 10+(G.induce W.innerTips).edgeSet.ncard=_ at price
  dsimp only [seedLoss];omega

#print axioms spent_count
#print axioms spent_edges
#print axioms spent_cap
#print axioms seed_edge_split
end JSP452Audit.StarHost.TenPortSupport
