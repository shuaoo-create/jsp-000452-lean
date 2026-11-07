import ZeroCutBudget
namespace JSP452Audit.StarHost
open SimpleGraph
variable {I : Type*} [Finite I]

/-- Two retained holes can cover every one of at most two prescribed
saturated roots. Each hole has at least three available roots and both
are adjacent to each prescribed root. -/
theorem allocate_two_hole_mates (A B J : Set I) (a3 : 3≤A.ncard) (b3 : 3≤B.ncard)
    (need : J.ncard≤2) (left : J⊆A) (right : J⊆B) :
    ∃p∈A,∃q∈B,p≠q ∧ J⊆{p,q} := by
  classical
  by_cases two : J.ncard=2
  · obtain ⟨p,q,ne,e⟩ := Set.ncard_eq_two.mp two
    have hp : p∈J := e ▸ (Set.mem_insert p {q})
    have hq : q∈J := e ▸ (Set.mem_insert_of_mem p (Set.mem_singleton q))
    exact ⟨p,left hp,q,right hq,ne,e.subset⟩
  by_cases one : J.ncard=1
  · obtain ⟨p,e⟩ := Set.ncard_eq_one.mp one
    have hp : p∈J := e ▸ Set.mem_singleton p
    obtain ⟨q,hq,away⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show ({p} : Set I).ncard<B.ncard by rw [Set.ncard_singleton];omega)
    exact ⟨p,left hp,q,hq,fun eq => away eq.symm,fun u hu =>
      Or.inl (Set.mem_singleton_iff.mp (e ▸ hu))⟩
  have empty : J=∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)
  obtain ⟨p,hp⟩ := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  obtain ⟨q,hq,away⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({p} : Set I).ncard<B.ncard by rw [Set.ncard_singleton];omega)
  exact ⟨p,hp,q,hq,fun eq => away eq.symm,empty ▸ Set.empty_subset _⟩

/-- The previous construction actually covers the selected root endpoints
as well as the two holes and the even clique. -/
theorem four_layer_remainder_with_two_full_roots {X : Type*} [Finite X] (H : SimpleGraph X)
    (C : Set X) (cl : H.IsClique C) (even : Even C.ncard) (a b p q : X)
    (ap : H.Adj a p) (bq : H.Adj b q)
    (out : ∀x,x∈({a,p,b,q} : Set X) → x∉C) (sep : Disjoint ({a,p} : Set X) ({b,q} : Set X))
    (cap : ∀x,Nat.card (H.neighborSet x)≤3)
    (cover : ∀x,Nat.card (H.neighborSet x)=3 → x∈C ∨ x∈({a,p,b,q} : Set X)) :
    admits_matching_remainder H 3 := by
  classical
  let e : C ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨P,hP,support⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique H e
    (fun {u v} ne => cl u.property v.property (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have ps : P.verts=C := support.trans (by ext x;exact ⟨fun ⟨u,eq⟩ => eq ▸ u.property,fun h => ⟨⟨x,h⟩,rfl⟩⟩)
  let A := H.subgraphOfAdj ap
  let B := H.subgraphOfAdj bq
  have ea : A.verts={a,p} := rfl
  have eb : B.verts={b,q} := rfl
  have pair := JSP452Audit.Padded.matching_sup_of_disjoint_verts H (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj ap)
    (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj bq) sep
  have all : (A⊔B).verts=({a,p,b,q} : Set X) := by
    rw [SimpleGraph.Subgraph.verts_sup,ea,eb]
    ext x;simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff];tauto
  have dis : Disjoint P.verts (A⊔B).verts := by
    rw [ps,all,Set.disjoint_left];exact fun _ hx he => out _ he hx
  have good := JSP452Audit.Padded.matching_sup_of_disjoint_verts H hP pair dis
  apply admits_remainder_of_full_cover H 3 (by decide) cap _ good
  intro x hx
  rw [SimpleGraph.Subgraph.verts_sup,ps,all]
  exact cover x hx

#print axioms allocate_two_hole_mates
#print axioms four_layer_remainder_with_two_full_roots
end JSP452Audit.StarHost
