import TwoRootsAtLargeClique
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem even_clique_two_edges (H : SimpleGraph X) (K : Set X) (cl : H.IsClique K)
    (even : Even K.ncard) (u v i j : X) (ui : H.Adj u i) (vj : H.Adj v j)
    (dis : Disjoint ({u,i}:Set X) {v,j}) (outside : Disjoint K (({u,i}:Set X)∪{v,j})) :
    ∃M : H.Subgraph,M.IsMatching ∧ K∪(({u,i}:Set X)∪{v,j})⊆M.verts := by
  let embed : K ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨P,pm,supp⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique H embed
    (fun {a b} ne => cl a.property b.property (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have ps : P.verts=K := supp.trans (by ext t; exact ⟨fun ⟨z,e⟩ => e ▸ z.property,fun h => ⟨⟨t,h⟩,rfl⟩⟩)
  let L := H.subgraphOfAdj ui
  let R := H.subgraphOfAdj vj
  have ls : L.verts={u,i} := rfl
  have rs : R.verts={v,j} := rfl
  have two := JSP452Audit.Padded.matching_sup_of_disjoint_verts H
    (Subgraph.IsMatching.subgraphOfAdj ui) (Subgraph.IsMatching.subgraphOfAdj vj) dis
  have away : Disjoint P.verts (L⊔R).verts := by rwa [Subgraph.verts_sup,ps,ls,rs]
  have combined := JSP452Audit.Padded.matching_sup_of_disjoint_verts H pm two away
  exact ⟨P⊔(L⊔R),combined,by rw [Subgraph.verts_sup,Subgraph.verts_sup,ps,ls,rs]⟩

/-- All roots except t are strictly below the degree bound. If t is full
it must reach at least one of the two retained singleton vertices. -/
theorem one_high_root_remainder (H : SimpleGraph X) (R K : Set X) (u v t : X) (D : ℕ)
    (four : 4≤D) (uv : u≠v) (ur : u∉R) (vr : v∉R) (uk : u∉K) (vk : v∉K)
    (tr : t∈R) (dis : Disjoint R K) (cl : H.IsClique K) (even : Even K.ncard)
    (cap : ∀w,Nat.card (H.neighborSet w)≤D-1)
    (full : ∀w,Nat.card (H.neighborSet w)=D-1 → w∈K ∨ w=u ∨ w=v ∨ w=t)
    (hit : Nat.card (H.neighborSet t)=D-1 → H.Adj u t ∨ H.Adj v t)
    (chooseU : ∀avoid,∃i∈R,i≠avoid ∧ H.Adj u i)
    (chooseV : ∀avoid,∃j∈R,j≠avoid ∧ H.Adj v j) : admits_matching_remainder H (D-1) := by
  classical
  obtain ⟨i,ir,j,jr,ne,ui,vj,keep⟩ : ∃i∈R,∃j∈R,i≠j ∧ H.Adj u i ∧ H.Adj v j ∧
      (Nat.card (H.neighborSet t)=D-1 → t=i ∨ t=j) := by
    by_cases top : Nat.card (H.neighborSet t)=D-1
    · rcases hit top with h|h
      · obtain ⟨j,jr,jt,vj⟩ := chooseV t; exact ⟨t,tr,j,jr,jt.symm,h,vj,fun _ => Or.inl rfl⟩
      · obtain ⟨i,ir,it,ui⟩ := chooseU t; exact ⟨i,ir,t,tr,it,ui,h,fun _ => Or.inr rfl⟩
    · obtain ⟨i,ir,_,ui⟩ := chooseU u
      obtain ⟨j,jr,ji,vj⟩ := chooseV i
      exact ⟨i,ir,j,jr,ji.symm,ui,vj,fun h => (top h).elim⟩
  have apart : Disjoint ({u,i}:Set X) {v,j} := by
    apply Set.disjoint_left.mpr
    rintro p (h|h) (k|k)
    · exact uv (h.symm.trans k)
    · exact ur ((h.symm.trans (Set.mem_singleton_iff.mp k)).symm ▸ jr)
    · exact vr (((Set.mem_singleton_iff.mp h).symm.trans k) ▸ ir)
    · exact ne ((Set.mem_singleton_iff.mp h).symm.trans (Set.mem_singleton_iff.mp k))
  have free : Disjoint K (({u,i}:Set X)∪{v,j}) := by
    apply Set.disjoint_left.mpr
    rintro p hp ((h|h)|h|h)
    · exact uk (h ▸ hp)
    · exact Set.disjoint_left.mp dis ir ((Set.mem_singleton_iff.mp h) ▸ hp)
    · exact vk (h ▸ hp)
    · exact Set.disjoint_left.mp dis jr ((Set.mem_singleton_iff.mp h) ▸ hp)
  obtain ⟨M,hm,support⟩ := even_clique_two_edges H K cl even u v i j ui vj apart free
  apply admits_remainder_of_full_cover H (D-1) (by omega) cap M hm
  intro w high
  apply support
  rcases full w high with k|eq|eq|eq
  · exact Or.inl k
  · exact Or.inr (Or.inl (Or.inl eq))
  · exact Or.inr (Or.inr (Or.inl eq))
  · rcases keep (eq ▸ high) with same|same
    · exact Or.inr (Or.inl (Or.inr (Set.mem_singleton_iff.mpr (eq.trans same))))
    · exact Or.inr (Or.inr (Or.inr (Set.mem_singleton_iff.mpr (eq.trans same))))

#print axioms one_high_root_remainder
end JSP452Audit.StarHost
