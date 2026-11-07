import DetailedBadMatching
import GoodSetSize
import EvenRegionLayerCost

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Choose low holes in every free large good component while preserving all
bad matched pairs and root mates in a single optimal original matching. -/
theorem good_and_bad_port_matching (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S)
    (opt : (freeFull G S D A).ncard = minimumExposure G D) (plan : BadPortPlan G S D A)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (inside : T ⊆ goodFullClass G S D)
    (split : ∀ c ∈ largeGoodPieces G S D T, GoodPortSplit c.toSimpleGraph D) :
    ∃ (M : G.Subgraph) (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp),
      M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      (exposedFull G M D).ncard = minimumExposure G D ∧
      M.vertsᶜ = freeHoleLabels G S A.place pick ∧
      exposedFull G M D = (fun c => (pick c).val.val) '' freeFull G S D A ∧
      (∀ a : S, M.Adj a.val (pick (A.place a)).val.val) ∧
      (∀ i : ↥plan.chosen, ∃ y z : i.val.val.supp, y ∈ portLow i.val.val.toSimpleGraph D ∧
        G.Adj (plan.root i).val y.val.val ∧ pick i.val.val ≠ y ∧ M.Adj y.val.val z.val.val ∧
        (pick i.val.val).val.val ∉ M.verts ∧ ¬G.Adj (pick i.val.val).val.val z.val.val ∧
        pick i.val.val ≠ z) ∧
      ∀ c ∈ T, c ∉ Set.range A.place →
        (pick c).val.val ∈ goodPortSet G S D T (largeGoodPieces G S D T) pick := by
  classical
  obtain ⟨base, links, degrees⟩ := choose_allocation_holes G S A D
  have piece (c : (G.induce Sᶜ).ConnectedComponent) :
      ∃ (v : c.supp) (J : c.toSimpleGraph.Subgraph), J.IsMatching ∧ J.verts = {t | t ≠ v} ∧
        (∀ a : S, A.place a = c → G.Adj a.val v.val.val) ∧
        (c ∉ Set.range A.place → (Nat.card (G.neighborSet v.val.val) = D ↔ allFullComponent G S D c)) ∧
        (c ∈ largeGoodPieces G S D T → c ∉ Set.range A.place → v ∈ portLow c.toSimpleGraph D) ∧
        ∀ (hb : c ∈ badFree G S D A) (hs : (⟨c,hb⟩ : ↥(badFree G S D A)) ∈ plan.chosen),
          ∃ y z : c.supp, y ∈ portLow c.toSimpleGraph D ∧
            G.Adj (plan.root ⟨⟨c,hb⟩,hs⟩).val y.val.val ∧ v ≠ y ∧ J.Adj y z ∧
            ¬c.toSimpleGraph.Adj v z := by
    by_cases selected : ∃ hb : c ∈ badFree G S D A, (⟨c,hb⟩ : ↥(badFree G S D A)) ∈ plan.chosen
    · obtain ⟨hb,hs⟩ := selected
      let i : ↥plan.chosen := ⟨⟨c,hb⟩,hs⟩
      obtain ⟨y, low, adj, v, distinct, J, hm, verts, z, pair, missing⟩ :=
        badPortIncidence_witness G S D (plan.root i) c (plan.edge i)
      exact ⟨v, J, hm, verts, fun a eq => (hb.1.1 ⟨a,eq⟩).elim,
        fun _ => ⟨fun _ => hb.1.2, fun full => full v⟩,
        (fun large _ => (hb.2 ((inside large.1).2)).elim),
        fun _ _ => ⟨y,z,low,adj,distinct,pair,missing⟩⟩
    · by_cases changeHole : c ∈ largeGoodPieces G S D T ∧ c ∉ Set.range A.place
      · obtain ⟨large, free⟩ := changeHole
        have lowCount := (split c large).low_count
        obtain ⟨v,low⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (portLow c.toSimpleGraph D).ncard ≠ 0)
        obtain ⟨N,perfect⟩ := (data c).2 v
        obtain ⟨J,hm,verts,_⟩ := lift_perfect_off_vertex_maximum _ v N perfect
        exact ⟨v,J,hm,verts,fun a eq => (free ⟨a,eq⟩).elim,
          fun _ => ⟨fun _ => (inside large.1).1, fun full => full v⟩,
          fun _ _ => low, fun hb hs => (selected ⟨hb,hs⟩).elim⟩
      obtain ⟨N,perfect⟩ := (data c).2 (base c)
      obtain ⟨J,hm,verts,_⟩ := lift_perfect_off_vertex_maximum _ (base c) N perfect
      refine ⟨base c,J,hm,verts,?_,degrees c,fun large free => (changeHole ⟨large,free⟩).elim,
        fun hb hs => (selected ⟨hb,hs⟩).elim⟩
      rintro a rfl
      exact links a
  choose pick P hm supports link degree lowFree witness using piece
  obtain ⟨M,hM,max,holes,keeps,roots⟩ := realize_prescribed_internal_matching G S tight
    (fun c => (data c).1) A.place pick (fun a => link (A.place a) a rfl) P hm supports
  have image := exposedFull_eq_label_image G S D A pick M holes degree
  refine ⟨M,pick,hM,max,(exposed_eq_freeFull G S D A pick M holes degree).trans opt,
    holes,image,roots,?_,?_⟩
  · intro i
    let c := i.val.val
    obtain ⟨y,z,low,adj,distinct,pair,missing⟩ := witness c i.val.property i.property
    have free : (pick c).val.val ∈ freeHoleLabels G S A.place pick := ⟨c,i.val.property.1.1,rfl⟩
    have miss : (pick c).val.val ∈ M.vertsᶜ := holes.symm ▸ free
    have yz := keeps c y z pair
    exact ⟨y,z,low,adj,distinct,yz,miss,missing,fun eq => miss (eq ▸ M.edge_vert yz.symm)⟩
  · intro c hc free
    apply (goodPortSet_member_iff G S D T (largeGoodPieces G S D T) pick c (pick c)).mpr
    by_cases large : c ∈ largeGoodPieces G S D T
    · exact ⟨hc,Or.inl ⟨large,lowFree c large free⟩⟩
    · exact ⟨hc,Or.inr ⟨large,rfl⟩⟩

#print axioms good_and_bad_port_matching
end JSP452Audit.StarHost
