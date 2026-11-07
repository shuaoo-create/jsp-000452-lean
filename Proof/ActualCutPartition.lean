import LabelledCutSides
import RefineCutPartition
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

noncomputable def preferredMatePart (H : SimpleGraph V) (N : H.Subgraph)
    (p j : ↥(N.vertsᶜ : Set V)) : Set V := by
  classical exact if j=p then mateBlock H N j.val∪zeroMateRegion H N else mateBlock H N j.val

/-- Extract the split partition on the same residual labels, from an actual
crossing of the original maximum matching, including all singleton holes. -/
theorem actual_cross_partition (H : SimpleGraph V) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (noEx : exceptionalMateRegion H N=∅)
    (p q : ↥(N.vertsᶜ : Set V)) (qp : q≠p)
    (conn : (H.induce (mateBlock H N p.val∪zeroMateRegion H N)).Preconnected)
    (limit : ∀ S : Set V,H.IsIndepSet S → S.ncard≤N.vertsᶜ.ncard+1)
    (others : ∀j : ↥(N.vertsᶜ : Set V), j≠p → H.IsClique (mateBlock H N j.val))
    (x : ↥(mateBlock H N p.val∪zeroMateRegion H N)) (y : mateBlock H N q.val)
    (edge : H.Adj x.val y.val) :
    let P := mateBlock H N p.val∪zeroMateRegion H N
    let W := preferredMatePart H N p
    ∃ L R : Set V, L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧ L∪R=P\{x.val} ∧
      (∃l∈L,H.Adj x.val l) ∧ (∃r∈R,H.Adj x.val r) ∧
      let F := splitCutParts W p L R
      (∀i j,i≠j → Disjoint (F i) (F j)) ∧ (∀i,H.IsClique (F i)) ∧
      (∀i,x.val∉F i) ∧ (∀v,v≠x.val → ∃i,v∈F i) ∧
      (∀i j,i≠j → ∀a∈F i,∀b∈F j,¬H.Adj a b) := by
  intro P W
  classical
  let J := ↥(N.vertsᶜ : Set V)
  let T (j:J) := mateBlock H N j.val
  let Z := zeroMateRegion H N
  have wp : W p=P := by simp [W,preferredMatePart,P]
  have plain (j:J) (h:j≠p) : W j=T j := by simp [W,T,preferredMatePart,h]
  have apart {i j:J} (ne:i≠j) : Disjoint (T i) (T j) :=
    different_mate_blocks_disjoint H N hm max i.val j.val i.property j.property
      (fun eq => ne (Subtype.ext eq))
  have disZ (j:J) : Disjoint (T j) Z := mate_block_disjoint_zero H N hm j.val j.property
  have dis (i j:J) (ne:i≠j) : Disjoint (W i) (W j) := by
    by_cases ip:i=p
    · subst i
      rw [wp,plain j (Ne.symm ne)]
      exact Set.disjoint_union_left.mpr ⟨apart ne,(disZ j).symm⟩
    by_cases jp:j=p
    · subst j
      rw [plain i ip,wp]
      exact Set.disjoint_union_right.mpr ⟨apart ne,disZ i⟩
    rw [plain i ip,plain j jp]
    exact apart ne
  have cover (a:V) : ∃j,a∈W j := by
    rcases mate_classes_cover H N hm a with ⟨u,hu,ha⟩|hz|ex
    · let j : J := ⟨u,hu⟩
      refine ⟨j,?_⟩
      by_cases same:j=p
      · rw [same,wp]
        exact Or.inl (same ▸ (ha : a∈T j))
      · rw [plain j same]; exact ha
    · exact ⟨p,wp ▸ (Or.inr hz : a∈P)⟩
    · exact (noEx ▸ ex : a∈(∅ : Set V)).elim
  have sep (i j:J) (ip:i≠p) (jp:j≠p) (diff:i≠j) :
      ∀a∈W i,∀b∈W j,¬H.Adj a b := by
    rw [plain i ip,plain j jp]
    exact clique_mate_blocks_separated H N hm max i.val j.val i.property j.property
      (fun h => diff (Subtype.ext h)) (others i ip) (others j jp)
  have pq : p.val≠q.val := fun eq => qp (Subtype.ext eq.symm)
  have port (i:J) (ip:i≠p) (a:V) (ha:a∈W p) (b:V) (hb:b∈W i) (ab:H.Adj a b) : a=x.val := by
    rw [wp] at ha
    rw [plain i ip] at hb
    have same := crossings_share_preferred_endpoint H N hm max p.val p.property conn limit q.val i.val
      q.property i.property pq (fun h => ip (Subtype.ext h.symm)) (others q qp) (others i ip)
      x ⟨a,ha⟩ y ⟨b,hb⟩ edge ab
    exact congrArg Subtype.val same
  have cut := preferred_cross_forces_cut_at_endpoint H N hm max p.property q.property pq limit (others q qp) x y edge
  obtain ⟨L,R,lne,rne,lr,sides,clL,clR,lrSep,xl,xr⟩ := labelled_cut_sides H P x conn
    (block_with_zero_region_small H N hm max p.val p.property limit) cut
  refine ⟨L,R,lne,rne,lr,sides,xl,xr,?_⟩
  apply split_cut_parts_structure H W p x.val L R (wp.symm ▸ sides) lr clL clR lrSep
    (wp.symm ▸ x.property) dis cover
  · intro i ip;rw [plain i ip];exact others i ip
  · exact sep
  · exact port

#print axioms actual_cross_partition
end JSP452Audit.StarHost
