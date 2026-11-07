import ExceptionalCliqueSeparation
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def exceptionalParts (H : SimpleGraph X) (N : H.Subgraph) (b : X) : Option ↥(N.vertsᶜ : Set X)→Set X
  | none => zeroMateRegion H N∪{b}
  | some j => mateBlock H N j.val

/-- After the heavy endpoint is removed, every surviving residual label is
in exactly one odd clique. All the ordinary nonempty holes retain their own
labels, while the matched partner b is placed with the original zero region. -/
theorem exceptional_cut_partition (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀T:Set X,H.IsIndepSet T → T.ncard≤N.vertsᶜ.ncard+1)
    (anti : H.IsClique (mateAntineighborhood H N.vertsᶜ))
    {a b : X} (heavy : holeHeavy H N a) (ab : N.Adj a b) :
    let C := exceptionalParts H N b
    exceptionalMateRegion H N={a,b} ∧
    (∀i j,i≠j → Disjoint (C i) (C j)) ∧ (∀i,H.IsClique (C i)) ∧
    (∀i,Odd (C i).ncard) ∧ (∀i,a∉C i) ∧ (∀v,v≠a → ∃i,v∈C i) ∧
    (∀i j,i≠j → ∀v∈C i,∀w∈C j,¬H.Adj v w) := by
  intro C
  let K := zeroMateRegion H N∪{b}
  let J := ↥(N.vertsᶜ : Set X)
  let T (j:J) := mateBlock H N j.val
  have edgeRegion : exceptionalMateRegion H N={a,b} := by
    ext v
    constructor
    · rintro ⟨u,vu,hv|hu⟩
      · exact Or.inl (heavy_endpoint_unique H N hm maximum anti hv heavy)
      · have ua := heavy_endpoint_unique H N hm maximum anti hu heavy
        subst u;exact Or.inr (Set.mem_singleton_iff.mpr (hm.eq_of_adj_left vu.symm ab))
    · rintro (eq|eq)
      · exact eq.symm ▸ (show a∈exceptionalMateRegion H N from ⟨b,ab,Or.inl heavy⟩)
      · exact (Set.mem_singleton_iff.mp eq).symm ▸
          (show b∈exceptionalMateRegion H N from ⟨a,ab.symm,Or.inr heavy⟩)
  have aE : a∈exceptionalMateRegion H N := ⟨b,ab,Or.inl heavy⟩
  have bE : b∈exceptionalMateRegion H N := ⟨a,ab.symm,Or.inr heavy⟩
  have disT (j:J) : Disjoint (T j) K :=
    Set.disjoint_union_right.mpr ⟨mate_block_disjoint_zero H N hm j.val j.property,
      (mate_block_disjoint_exceptional H N hm j.val j.property).mono_right (Set.singleton_subset_iff.mpr bE)⟩
  obtain ⟨cl,odd,ordinary⟩ := exceptional_parts_are_separated H N hm maximum limit anti heavy ab
  have d (i j : Option J) (ne:i≠j) : Disjoint (C i) (C j) := by
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (ne rfl)
      | some t => exact (disT t).symm
    | some u =>
      cases j with
      | none => exact disT u
      | some t =>
        exact different_mate_blocks_disjoint H N hm maximum u.val t.val u.property t.property
          (fun eq => ne (congrArg some (Subtype.ext eq)))
  refine ⟨edgeRegion,d,?_,?_,?_,?_,?_⟩
  · intro i
    cases i with
    | none => exact cl
    | some t => exact (ordinary t.val t.property).1
  · intro i
    cases i with
    | none => exact odd
    | some t => exact mateBlock_odd H N hm t.val t.property
  · intro i
    cases i with
    | none =>
      rintro (az|eq)
      · exact Set.disjoint_left.mp (zero_region_disjoint_exceptional H N hm) az aE
      · exact (N.adj_sub ab).ne (Set.mem_singleton_iff.mp eq)
    | some t => exact fun h => Set.disjoint_left.mp (mate_block_disjoint_exceptional H N hm _ t.property) h aE
  · intro v va
    rcases mate_classes_cover H N hm v with ⟨u,hu,mem⟩|hz|he
    · exact ⟨some ⟨u,hu⟩,mem⟩
    · exact ⟨none,Or.inl hz⟩
    · rw [edgeRegion] at he
      exact ⟨none,Or.inr ((Set.mem_insert_iff.mp he).resolve_left va)⟩
  · intro i j ne v hv w hw edge
    cases i with
    | none =>
      cases j with
      | none => exact ne rfl
      | some t => exact (ordinary t.val t.property).2 w hw v hv edge.symm
    | some u =>
      cases j with
      | none => exact (ordinary u.val u.property).2 v hv w hw edge
      | some t =>
        exact clique_mate_blocks_separated H N hm maximum u.val t.val u.property t.property
          (fun eq => ne (congrArg some (Subtype.ext eq))) (ordinary u.val u.property).1
          (ordinary t.val t.property).1 v hv w hw edge

#print axioms exceptional_cut_partition
end JSP452Audit.StarHost
