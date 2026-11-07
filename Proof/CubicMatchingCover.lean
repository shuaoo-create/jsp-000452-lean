import CubicPairInventory
namespace JSP452Audit.StarHost
open SimpleGraph

def CubicPairFamily.supportGraph {X I : Type*} (P:CubicPairFamily X I) : SimpleGraph X where
  Adj a b := ∃i,(a=P.left i ∧ b=P.right i) ∨ (a=P.right i ∧ b=P.left i)
  symm := ⟨by
    rintro u v ⟨i,h|h⟩
    · exact ⟨i,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨i,Or.inl ⟨h.2,h.1⟩⟩⟩
  loopless := ⟨by
    rintro a ⟨i,h|h⟩
    · exact P.distinct i (h.1.symm.trans h.2)
    · exact P.distinct i (h.2.symm.trans h.1)⟩

/-- An ordinary maximum matching in the pair-support graph saves one
selected label per matched edge, even if the label covering that edge lives
outside the white set. -/
theorem pair_matching_gives_cover {X : Type*} [Finite X] (G:SimpleGraph X) (U:Set X) (K:SimpleGraph U)
    (witness : ∀u v,K.Adj u v → ∃w:X,(u.val=w ∨ G.Adj u.val w) ∧ (v.val=w ∨ G.Adj v.val w)) :
    ∃S:Set X,(∀x∈U,x∈S ∨ ∃w∈S,G.Adj x w) ∧ S.ncard+matchingEdges K≤U.ncard := by
  classical
  obtain ⟨M,hm,max⟩ := exists_maximum_matching K
  have covered (e:M.edgeSet) : ∃w:X,
      ((e.val.out.1:X)=w ∨ G.Adj e.val.out.1.val w) ∧ ((e.val.out.2:X)=w ∨ G.Adj e.val.out.2.val w) := by
    apply witness
    have edge : M.Adj e.val.out.1 e.val.out.2 := by
      have same : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
      change s(e.val.out.1,e.val.out.2)∈M.edgeSet;rw [same];exact e.property
    exact M.adj_sub edge
  choose pick hits using covered
  let chosen := pick '' (Set.univ:Set M.edgeSet)
  let free := Subtype.val '' (M.vertsᶜ:Set U)
  let S := chosen∪free
  refine ⟨S,?_,?_⟩
  · intro x inside
    let u : U := ⟨x,inside⟩
    by_cases yes:u∈M.verts
    · obtain ⟨v,edge,_⟩ := hm yes
      let e : M.edgeSet := ⟨s(u,v),edge⟩
      have mem : u∈e.val := Sym2.mem_mk_left _ _
      have sameEnds : s(e.val.out.1,e.val.out.2)=e.val := e.val.out_eq
      rw [←sameEnds,Sym2.mem_iff] at mem
      have selected : pick e∈S := Or.inl ⟨e,Set.mem_univ _,rfl⟩
      have adj : x=pick e ∨ G.Adj x (pick e) := by
        rcases mem with left|right
        · have h := (hits e).1;change (u.val=pick e ∨ G.Adj u.val (pick e));rwa [left]
        · have h := (hits e).2;change (u.val=pick e ∨ G.Adj u.val (pick e));rwa [right]
      rcases adj with same|joins
      · exact Or.inl (same.symm ▸ selected)
      · exact Or.inr ⟨pick e,selected,joins⟩
    · exact Or.inl (Or.inr ⟨u,yes,rfl⟩)
  · have atMost := Set.ncard_image_le (s:=(Set.univ:Set M.edgeSet)) (f:=pick)
    rw [Set.ncard_univ,Nat.card_coe_set_eq] at atMost
    change chosen.ncard≤M.edgeSet.ncard at atMost
    have size : free.ncard=(M.vertsᶜ:Set U).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    have rest := Set.ncard_add_ncard_compl M.verts
    rw [Nat.card_coe_set_eq,matching_vertices_eq_twice_edges hm,max] at rest
    have union := Set.ncard_union_le chosen free
    change (chosen∪free).ncard+matchingEdges K≤U.ncard
    omega

#print axioms pair_matching_gives_cover
end JSP452Audit.StarHost
