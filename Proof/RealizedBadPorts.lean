import DisjointOriginalBadPorts
import PrescribedInternalMatching

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Realize every bad-port certificate of a plan inside the same
exposure-minimizing maximum matching of the original graph. -/
theorem realize_bad_port_plan (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S)
    (opt : (freeFull G S D A).ncard = minimumExposure G D) (plan : BadPortPlan G S D A) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      (exposedFull G M D).ncard = minimumExposure G D ∧
      (∀ i : ↥plan.chosen, ∃ y v z : i.val.val.supp, y ∈ portLow i.val.val.toSimpleGraph D ∧
        G.Adj (plan.root i).val y.val.val ∧ v ≠ y ∧ M.Adj y.val.val z.val.val ∧
        v.val.val ∉ M.verts ∧ ¬G.Adj v.val.val z.val.val) ∧
      (∀ a : ↥S, ∃ b : (A.place a).supp, M.Adj a.val b.val.val) ∧
      (∃ pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp,
        M.vertsᶜ = freeHoleLabels G S A.place pick ∧
        ∀ a : ↥S, M.Adj a.val (pick (A.place a)).val.val) := by
  classical
  obtain ⟨base, links, degrees⟩ := choose_allocation_holes G S A D
  have piece (c : (G.induce Sᶜ).ConnectedComponent) :
      ∃ (v : c.supp) (J : c.toSimpleGraph.Subgraph), J.IsMatching ∧ J.verts = {t | t ≠ v} ∧
        (∀ a : S, A.place a = c → G.Adj a.val v.val.val) ∧
        (c ∉ Set.range A.place → (Nat.card (G.neighborSet v.val.val) = D ↔ allFullComponent G S D c)) ∧
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
        fun _ _ => ⟨y,z,low,adj,distinct,pair,missing⟩⟩
    · obtain ⟨N,perfect⟩ := (data c).2 (base c)
      obtain ⟨J,hm,verts,_⟩ := lift_perfect_off_vertex_maximum _ (base c) N perfect
      refine ⟨base c,J,hm,verts,?_,degrees c,fun hb hs => (selected ⟨hb,hs⟩).elim⟩
      rintro a rfl
      exact links a
  choose pick P hm supports link degree witness using piece
  obtain ⟨M,hM,max,holes,keeps,roots⟩ := realize_prescribed_internal_matching G S tight
    (fun c => (data c).1) A.place pick (fun a => link (A.place a) a rfl) P hm supports
  refine ⟨M,hM,max,(exposed_eq_freeFull G S D A pick M holes degree).trans opt,?_,
    fun a => ⟨pick (A.place a), roots a⟩, pick, holes, roots⟩
  intro i
  let c := i.val.val
  obtain ⟨y,z,low,adj,distinct,pair,missing⟩ := witness c i.val.property i.property
  have free : (pick c).val.val ∈ freeHoleLabels G S A.place pick := ⟨c,i.val.property.1.1,rfl⟩
  have uncovered : (pick c).val.val ∈ M.vertsᶜ := holes.symm ▸ free
  exact ⟨y,pick c,z,low,adj,distinct,keeps c y z pair,uncovered,missing⟩

#print axioms realize_bad_port_plan
end JSP452Audit.StarHost
