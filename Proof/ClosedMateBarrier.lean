import MatePartitionOrder
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- The set is a union of whole matched pairs and arbitrary holes. -/
def mateClosed {H : SimpleGraph X} (N : H.Subgraph) (S : Set X) : Prop :=
  ∀ ⦃a b⦄,N.Adj a b → a∈S → b∈S

/-- If a closed region contained an exposed point and were perfectly
matchable, replacing N inside it would strictly enlarge its support. -/
theorem closed_region_with_hole_no_perfect [Finite X] (H : SimpleGraph X)
    (N : H.Subgraph) (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (S : Set X) (closed : mateClosed N S) (w : X) (hw : w∉N.verts) (inside : w∈S) :
    ¬∃ P : (H.induce S).Subgraph,P.IsPerfectMatching := by
  rintro ⟨P,perfect⟩
  let e := SimpleGraph.Embedding.induce (G:=H) S
  let L := P.map e.toHom
  have ml : L.IsMatching := perfect.1.map e.toHom e.injective
  have cover : ∀x,x∈S → x∈L.verts := by
    intro x h
    exact ⟨⟨x,h⟩,Subgraph.isSpanning_iff.mp perfect.2 ▸ Set.mem_univ _,rfl⟩
  let B : H.Subgraph := {
    verts := N.verts \ S
    Adj a b := N.Adj a b ∧ a∉S ∧ b∉S
    adj_sub := fun h => N.adj_sub h.1
    edge_vert := fun h => ⟨N.edge_vert h.1,h.2.1⟩
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩ }
  have mb : B.IsMatching := by
    intro a ha
    obtain ⟨b,ab,_⟩ := hm ha.1
    have bn : b∉S := fun hb => ha.2 (closed ab.symm hb)
    exact ⟨b,⟨ab,ha.2,bn⟩,fun z hz => hm.eq_of_adj_left hz.1 ab⟩
  have apart : Disjoint L.verts B.verts := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,_,rfl⟩ b
    exact b.2 x.property
  let J := L ⊔ B
  have mj : J.IsMatching := JSP452Audit.Padded.matching_sup_of_disjoint_verts H ml mb apart
  have inc : N.verts ⊆ J.verts := by
    intro x hx
    by_cases h : x∈S
    · exact Or.inl (cover x h)
    · exact Or.inr ⟨hx,h⟩
  have bigger := Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr
    ⟨inc,w,(show w∈J.verts from Or.inl (cover w inside)),hw⟩)
  rw [matching_vertices_eq_twice_edges hm,matching_vertices_eq_twice_edges mj,maximum] at bigger
  have upper := le_matchingEdges mj
  omega

theorem mateClosed.union {H : SimpleGraph X} {N : H.Subgraph} {S T : Set X}
    (s : mateClosed N S) (t : mateClosed N T) : mateClosed N (S∪T) := by
  intro a b edge h
  exact h.elim (fun hs => Or.inl (s edge hs)) (fun ht => Or.inr (t edge ht))

theorem pointed_mate_block_closed (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) : mateClosed N (mateBlock H N w) := by
  rintro a b ab (eq|⟨y,ay,la,ly,t⟩)
  · exact False.elim (hw (eq ▸ N.edge_vert ab))
  · have eq := hm.eq_of_adj_left ab ay
    subst b
    exact (mateBlock_pair_mem H N w ay la ly t).2

theorem zero_mate_region_closed (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching) :
    mateClosed N (zeroMateRegion H N) := by
  rintro a b ab ⟨y,ay,aa,yy⟩
  have eq := hm.eq_of_adj_left ab ay
  subst b
  exact ⟨a,ay.symm,yy,aa⟩

/-- Both unions in Zhao's two-block obstruction are evaluated in the actual
residual graph. The argument even allows exceptional edges elsewhere. -/
theorem two_mate_blocks_not_perfect [Finite X] (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges H)
    (w u : X) (hw : w∉N.verts) (hu : u∉N.verts) :
    let T := mateBlock H N w ∪ mateBlock H N u
    (¬∃P : (H.induce T).Subgraph,P.IsPerfectMatching) ∧
      (¬∃P : (H.induce (T ∪ zeroMateRegion H N)).Subgraph,P.IsPerfectMatching) := by
  intro T
  have inT : w∈T := Or.inl (mateBlock_self H N w)
  have ct := (pointed_mate_block_closed H N hm w hw).union (pointed_mate_block_closed H N hm u hu)
  exact ⟨closed_region_with_hole_no_perfect H N hm max T ct w hw inT,
    closed_region_with_hole_no_perfect H N hm max _ (ct.union (zero_mate_region_closed H N hm))
      w hw (Or.inl inT)⟩

#print axioms closed_region_with_hole_no_perfect
#print axioms two_mate_blocks_not_perfect
end JSP452Audit.StarHost
