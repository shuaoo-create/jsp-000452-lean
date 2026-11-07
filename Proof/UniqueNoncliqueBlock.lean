import ExposableMatePair
import ExposableCross
import ManyMateBlocks
import UnpaidMateDecomposition

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Select two distinct, independent original labels of a nonclique block.
Each label can be exposed by a matching of that same block. -/
private theorem exposable_two_set (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (w : X) (hole : w∉N.verts)
    (bad : ¬H.IsClique (mateBlock H N w)) :
    ∃ A : Set X, A⊆mateBlock H N w ∧ A.ncard=2 ∧ H.IsIndepSet A ∧
      ∀x∈A, ∃hx:x∈mateBlock H N w,
        ExposablePoint (H.induce (mateBlock H N w)) ⟨x,hx⟩ := by
  let T := mateBlock H N w
  have incomplete : ¬(H.induce T).IsClique Set.univ := by
    intro clique
    apply bad
    intro x hx y hy ne
    exact @clique ⟨x,hx⟩ (Set.mem_univ _) ⟨y,hy⟩ (Set.mem_univ _)
      (fun eq => ne (congrArg Subtype.val eq))
  have seed : ∃a, ExposablePoint (H.induce T) a :=
    ⟨⟨w,mateBlock_self H N w⟩,mate_block_root_exposable H N hm w hole⟩
  obtain ⟨a,b,different,noEdge,ea,eb⟩ := exposable_pair_in_nonclique (H.induce T)
    (mateBlock_connected H N w) seed incomplete
  have ab : a.val≠b.val := fun eq => different (Subtype.ext eq)
  have noAB : ¬H.Adj a.val b.val := noEdge
  refine ⟨{a.val,b.val},?_,Set.ncard_pair ab,?_,?_⟩
  · rintro x (rfl|eq)
    · exact a.property
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ b.property
  · intro x hx y hy ne edge
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
      first | exact ne rfl | exact noAB edge | exact noAB edge.symm
  · intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact ⟨a.property,ea⟩
    · exact ⟨b.property,eb⟩

/-- Two genuinely different holes cannot both own nonclique blocks. Two
exposable nonneighbors from each block would form four independent labels,
but R75 allows only three in a two-block family. -/
theorem nonclique_mate_blocks_unique (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (nonW : ¬H.IsClique (mateBlock H N w)) (nonU : ¬H.IsClique (mateBlock H N u)) :
    w=u := by
  classical
  by_contra different
  obtain ⟨A,Ain,twoA,indA,expA⟩ := exposable_two_set H N hm w hw nonW
  obtain ⟨B,Bin,twoB,indB,expB⟩ := exposable_two_set H N hm u hu nonU
  have apart := (different_mate_blocks_disjoint H N hm maximum w u hw hu different).mono Ain Bin
  have cross (a : X) (ha : a∈A) (b : X) (hb : b∈B) : ¬H.Adj a b := by
    obtain ⟨wa,ea⟩ := expA a ha
    obtain ⟨ub,eb⟩ := expB b hb
    exact exposable_block_vertices_nonadjacent H N hm maximum w u hw hu different ⟨a,wa⟩ ⟨b,ub⟩ ea eb
  have united : H.IsIndepSet (A∪B) := by
    rintro a (ha|ha) b (hb|hb) ne edge
    · exact indA ha hb ne edge
    · exact cross a ha b hb edge
    · exact cross b hb a ha edge.symm
    · exact indB ha hb ne edge
  have roots : ({w,u} : Set X)⊆N.vertsᶜ := by
    rintro x (rfl|eq)
    · exact hw
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ hu
  have bound := many_blocks_independent_bound H N hm maximum limit {w,u}
    roots (A∪B) united (by
      rintro x (ha|hb)
      · exact ⟨w,Or.inl rfl,Ain ha⟩
      · exact ⟨u,Or.inr rfl,Bin hb⟩)
  rw [Set.ncard_union_eq apart,twoA,twoB,Set.ncard_pair different] at bound
  omega

/-- If a distinguished hole was chosen to own a nonclique whenever one
exists, every other hole owns a clique. This includes the all-clique case. -/
theorem other_mate_blocks_clique_of_preferred (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤N.vertsᶜ.ncard+1)
    (w₀ : X) (root : w₀∉N.verts)
    (preferred : (∃w, w∉N.verts ∧ ¬H.IsClique (mateBlock H N w)) →
      ¬H.IsClique (mateBlock H N w₀)) :
    ∀u,u∉N.verts → u≠w₀ → H.IsClique (mateBlock H N u) := by
  intro u hole different
  by_contra nonU
  exact different (nonclique_mate_blocks_unique H N hm maximum limit u w₀ hole root
    nonU (preferred ⟨u,hole,nonU⟩))

omit [Finite X] in
private theorem original_clique_iff (Q : SimpleGraph X) (I : Set X) (B : Set ↥(Iᶜ : Set X)) :
    Q.IsClique (Subtype.val '' B) ↔ (Q.induce Iᶜ).IsClique B := by
  constructor
  · intro clique a ha b hb distinct
    exact clique ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ (fun eq => distinct (Subtype.ext eq))
  · rintro clique _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne
    exact clique ha hb (fun eq => ne (congrArg Subtype.val eq))

/-- Count bad roots on the original vertex labels. The underlying block is
tested for cliquehood in Q after restoring those labels. -/
theorem labeled_nonclique_mate_count (Q : SimpleGraph X) (I : Set X)
    (N : (Q.induce Iᶜ).Subgraph) (W : Set X)
    (matching : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (labels : Subtype.val '' N.vertsᶜ=W) (gap : W.ncard+1=I.ncard) :
    let H := Q.induce Iᶜ
    let bad := {w : ↥(Iᶜ : Set X) | w∉N.verts ∧ ¬Q.IsClique (Subtype.val '' mateBlock H N w)}
    (Subtype.val '' bad).ncard≤1 ∧ Subtype.val '' bad ⊆ W := by
  intro H bad
  have rootGap := gap
  rw [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at rootGap
  have limit (A : Set ↥(Iᶜ : Set X)) (ind : H.IsIndepSet A) : A.ncard≤N.vertsᶜ.ncard+1 := by
    have mapped : Q.IsIndepSet (Subtype.val '' A) := by
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne edge
      exact ind ha hb (fun eq => ne (congrArg Subtype.val eq)) edge
    have bound := largest _ mapped
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←rootGap] at bound
  constructor
  · rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    apply (Set.ncard_le_one (Set.toFinite _)).mpr
    intro w hw u hu
    exact nonclique_mate_blocks_unique H N matching maximum limit w u hw.1 hu.1
      (fun clique => hw.2 ((original_clique_iff Q I _).mpr clique))
      (fun clique => hu.2 ((original_clique_iff Q I _).mpr clique))
  · rintro _ ⟨w,hw,rfl⟩
    exact labels ▸ ⟨w,hw.1,rfl⟩

/-- The original unpaid regular component admits a maximum independent
set and an exposing matching with at most one exceptional nonclique root.
Both the root image and each block image retain Q's original vertex labels. -/
theorem unpaid_original_nonclique_mate_count [Nonempty X] (Q : SimpleGraph X)
    (D k : ℕ) (large : 3≤D) (regular : ∀x,Nat.card (Q.neighborSet x)=D)
    (critical : PerfectAfterEveryDeletion Q) (unpaid : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧
      3≤I.ncard ∧ v∈I ∧ M.IsMatching ∧ M.verts={x|x≠v} ∧
      M.edgeSet.ncard=matchingEdges Q ∧
      let H := Q.induce Iᶜ
      let N := restrictedOutsideMatching Q I M
      let W := independentMateLabels Q I v M
      let bad := {w : ↥(Iᶜ : Set X) | w∉N.verts ∧ ¬Q.IsClique (Subtype.val '' mateBlock H N w)}
      Subtype.val '' N.vertsᶜ=W ∧ (Subtype.val '' bad).ncard≤1 ∧ Subtype.val '' bad⊆W := by
  obtain ⟨I,v,M,ind,largest,three,vi,matching,expose,maxM,hn,rank,_,labels,gap,_,_,_⟩ :=
    unpaid_regular_mate_decomposition Q D k large regular critical unpaid
  obtain ⟨count,inside⟩ := labeled_nonclique_mate_count Q I (restrictedOutsideMatching Q I M)
    (independentMateLabels Q I v M) hn rank largest labels gap
  exact ⟨I,v,M,ind,largest,three,vi,matching,expose,maxM,labels,count,inside⟩

#print axioms nonclique_mate_blocks_unique
#print axioms other_mate_blocks_clique_of_preferred
#print axioms labeled_nonclique_mate_count
#print axioms unpaid_original_nonclique_mate_count
end JSP452Audit.StarHost

