import ActualFinalSevenDegreeMenuCost
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem nine_neighbors_or_single_tip (cap : ∀x,Nat.card (G.neighborSet x)≤9) (i : Fin 2) (I : Set X)
    (sub : I⊆R.box i) (ind : G.IsIndepSet I) : I.ncard+9≤(R.box i).ncard := by
  classical
  let U := R.box i
  by_cases lonely : I⊆{(R.port i).tip}
  · have size := Set.ncard_le_ncard lonely
    rw [Set.ncard_singleton] at size
    obtain ⟨ord,large⟩ := R.inner i
    change (R.box i).ncard=2*R.capacity i+1 at ord
    change 5≤R.capacity i at large;omega
  · obtain ⟨x,hx,diff⟩ := Set.not_subset.mp lonely
    have full := uniform_tight_piece_full G 3 6 cap R.K.S R.K.T (R.select i).val.val (R.select i).val.property x (sub hx)
    have neigh : G.neighborSet x⊆U\I := by
      intro y edge
      have chosen : y∈U := by
        by_contra no
        exact diff ((R.port i).only x (sub hx) y no edge).1
      exact ⟨chosen,fun yy => ind hx yy (G.ne_of_adj edge) edge⟩
    have cost := Set.ncard_le_ncard neigh
    rw [←Nat.card_coe_set_eq,full] at cost
    have count := Set.ncard_sdiff_add_ncard_of_subset sub
    change (U\I).ncard+I.ncard=(R.box i).ncard at count
    omega

theorem combined_nine_neighbor_saving (cap : ∀x,Nat.card (G.neighborSet x)≤9)
    (I : Set X) (inside : I⊆R.chosen) (ind : G.IsIndepSet I) : I.ncard+16≤2*R.totalCapacity := by
  let A := I∩R.box 0
  let B := I∩R.box 1
  have split : A∪B=I := by
    ext x;exact ⟨fun h => h.elim And.left And.left,
      fun h => (inside h).elim (fun a => Or.inl ⟨h,a⟩) (fun b => Or.inr ⟨h,b⟩)⟩
  have x0 : A⊆R.box 0 := Set.inter_subset_right
  have x1 : B⊆R.box 1 := Set.inter_subset_right
  have first := R.nine_neighbors_or_single_tip cap 0 A x0 (fun {_} h {_} k ne => ind h.1 k.1 ne)
  have next := R.nine_neighbors_or_single_tip cap 1 B x1 (fun {_} h {_} k ne => ind h.1 k.1 ne)
  have size := Set.ncard_union_eq (R.disjoint_boxes.mono x0 x1)
  rw [split] at size
  have a0 := (R.inner 0).1
  have a1 := (R.inner 1).1
  change (R.box 0).ncard=2*R.capacity 0+1 at a0
  change (R.box 1).ncard=2*R.capacity 1+1 at a1
  change I.ncard+16≤2*(R.capacity 0+R.capacity 1)
  omega

#print axioms nine_neighbors_or_single_tip
#print axioms combined_nine_neighbor_saving
end JSP452Audit.StarHost.NinePortRegion
