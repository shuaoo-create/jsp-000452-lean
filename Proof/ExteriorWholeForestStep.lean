import PersistentExteriorDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem whole_forest_in_surviving_exterior {s t r D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (W : Set X) (ext : W⊆K.rest)
    (room : matchingEdges (G.induce K.core)+K.roots.ncard+r+W.ncard<t) :
    (forest n).IsContained (G.induce (K.rest\W)) := by
  obtain ⟨ap,ab,pb,_⟩ := region_partition G K.barrier K.pieces
  change Disjoint K.roots K.core at ap
  change Disjoint K.roots K.rest at ab
  change Disjoint K.core K.rest at pb
  obtain ⟨cover,_,sep⟩ := core_rest_partition G K.barrier K.pieces
  change K.core∪K.rest=K.rootsᶜ at cover
  let U := K.roots∪W
  have dis : Disjoint K.roots W := ab.mono_right ext
  have size : U.ncard=K.roots.ncard+W.ncard := Set.ncard_union_eq dis
  have part : (K.rest\W)∪K.core=Uᶜ := by
    ext v
    constructor
    · rintro (⟨vr,away⟩|vc) (root|w)
      · exact Set.disjoint_left.mp ab root vr
      · exact away w
      · exact Set.disjoint_left.mp ap root vc
      · exact Set.disjoint_left.mp pb vc (ext w)
    · intro hv
      have no : v∈K.rootsᶜ := fun a => hv (Or.inl a)
      rcases (show v∈K.core∪K.rest from cover.symm ▸ no) with core|rest
      · exact Or.inr core
      · exact Or.inl ⟨rest,fun w => hv (Or.inr w)⟩
  let e := regionSumIso G Uᶜ (K.rest\W) K.core part (pb.symm.mono_left Set.sdiff_subset)
    (fun _ vr _ vc edge => sep vc vr.1 edge.symm)
  have shifted := row_delete_set G U _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  exact sum_row_forces_whole_left _ _ hs n m pn pm (forcingRow_of_iso e.symm shifted) (by omega)

private theorem degree_on_independent_full_set (G : SimpleGraph X) (U : Set X) (D : ℕ)
    (full : ∀v∈U,Nat.card (G.neighborSet v)=D) (ind : G.IsIndepSet U) :
    G.edgeSet.ncard=(G.induce Uᶜ).edgeSet.ncard+D*U.ncard := by
  have empty : G.induce U=⊥ := by
    ext a b;exact ⟨fun e => ind a.property b.property
      (show G.Adj a.val b.val from e).ne e,False.elim⟩
  have count := root_deletion_cost G U
  rw [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero,degree_sum_full G U D full] at count
  simpa [Nat.mul_comm] using count

/-- The whole first forest in the remaining exterior supplies a new
degree-D center, with every original neighbour still in that exterior. -/
theorem choose_full_exterior_center {s t r D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (W : Set X) (ext : W⊆K.rest)
    (room : matchingEdges (G.induce K.core)+K.roots.ncard+r+W.ncard<t) :
    ∃v∈K.rest\W,Nat.card (G.neighborSet v)=D ∧ G.neighborSet v⊆K.rest\W := by
  obtain ⟨f⟩ := whole_forest_in_surviving_exterior G K hs n m hn hm pn pm row W ext room
  let T := K.rest\W
  let i : Fin s := ⟨0,hs⟩
  let v : T := f (center n i)
  let nb (j : Fin (n i)) : (G.induce T).neighborSet v :=
    ⟨f (leaf n ⟨i,j⟩),f.toHom.map_adj (starEdge n ⟨i,j⟩)⟩
  have inj : Function.Injective nb := by
    intro j k eq
    have h := f.injective (congrArg (fun z : (G.induce T).neighborSet v => z.val) eq)
    change leaf n ⟨i,j⟩=leaf n ⟨i,k⟩ at h
    have same := congrArg (fun z : Vertices n => z.2.val) h
    apply Fin.ext
    simpa [leaf] using same
  have lower := Nat.card_le_card_of_injective nb inj
  rw [Nat.card_fin,show n i=D from head,induced_degree_intersection] at lower
  have upper := cap v.val
  have full : (G.neighborSet v.val).ncard≤D := (Nat.card_coe_set_eq _).symm.le.trans upper
  have eq := Set.eq_of_subset_of_ncard_le (Set.inter_subset_left (s:=G.neighborSet v.val) (t:=T)) (by omega)
  have size := (Set.ncard_le_ncard (Set.inter_subset_left (s:=G.neighborSet v.val) (t:=T)))
  rw [←Nat.card_coe_set_eq (G.neighborSet v.val)] at size
  exact ⟨v.val,v.property,by omega,fun w hw => (show w∈G.neighborSet v.val∩T from eq.symm ▸ hw).2⟩

#print axioms whole_forest_in_surviving_exterior
#print axioms choose_full_exterior_center
end JSP452Audit.StarHost
