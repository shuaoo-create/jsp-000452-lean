import ExceptionalBigLabels
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An even clique and disjoint genuine crossing edges give a numerical
lower bound on the maximum matching of the very graph containing them. -/
theorem even_clique_and_edge_family_rank {J : Type*} [Finite J] (Q : SimpleGraph X)
    (C : Set X) (cl : Q.IsClique C) (even : Even C.ncard) (l r : J ↪ X)
    (edge : ∀j,Q.Adj (l j) (r j)) (apart : Disjoint (Set.range l) (Set.range r))
    (free : Disjoint C (Set.range l∪Set.range r)) :
    C.ncard+2*Nat.card J ≤ 2*matchingEdges Q := by
  classical
  let inc : C ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨M,hm,supp⟩ := JSP452Audit.Padded.existsMatchingOnEvenClique Q inc
    (fun {v w} ne => cl v.property w.property (fun eq => ne (Subtype.ext eq)))
    (by rwa [Nat.card_coe_set_eq])
  have mv : M.verts=C := supp.trans (by ext v; exact ⟨fun ⟨x,h⟩ => h ▸ x.property,fun h => ⟨⟨v,h⟩,rfl⟩⟩)
  let N := JSP452Audit.Padded.pairFamily Q l r edge
  have mn := JSP452Audit.Padded.pairFamily_isMatching Q l r edge apart
  have nv : N.verts=Set.range l∪Set.range r := rfl
  have dis : Disjoint M.verts N.verts := by rwa [mv,nv]
  have matchM := JSP452Audit.Padded.matching_sup_of_disjoint_verts Q hm mn dis
  have count := matching_vertices_eq_twice_edges matchM
  have bound := le_matchingEdges matchM
  have rc (e:J↪X) : (Set.range e).ncard=Nat.card J :=
    (Nat.card_coe_set_eq _).symm.trans (Nat.card_congr (Equiv.ofInjective e e.injective)).symm
  rw [Subgraph.verts_sup,Set.ncard_union_eq dis,mv,nv,Set.ncard_union_eq apart,rc,rc] at count
  omega

theorem heavy_clique_host_order (Q : SimpleGraph X) (I : Set X) (D : ℕ)
    (s : HeavyCliqueFrame Q I D) : Nat.card X=I.ncard+I.ncard+(D-1) := by
  let C := s.cliquePart
  let S := s.singles
  have di : Disjoint I S := Set.disjoint_left.mpr (fun _ hi hs => s.sOut hs hi)
  have dc : Disjoint (I∪S) C := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_left.mpr (fun _ hi hc => s.cOut hc hi),s.dis⟩
  have aa : s.pivot∉I∪S∪C := fun h => h.elim (fun h => h.elim s.ai s.as_) s.ac
  have cover : insert s.pivot (I∪S∪C)=Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    rcases s.cover v with hi|ha|hs|hc
    · exact Or.inr (Or.inl (Or.inl hi))
    · exact Or.inl ha
    · exact Or.inr (Or.inl (Or.inr hs))
    · exact Or.inr (Or.inr hc)
  have count := congrArg Set.ncard cover
  rw [Set.ncard_insert_of_notMem aa,Set.ncard_union_eq dc,Set.ncard_union_eq di,Set.ncard_univ] at count
  have cardS : S.ncard+1=I.ncard := s.count
  have cardC : C.ncard=D-1 := s.order
  omega

theorem independent_cut_leaves_half_rank [Nonempty X] (Q : SimpleGraph X) (I : Set X)
    (D : ℕ) (four : 4≤D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (s : HeavyCliqueFrame Q I D) (z:X) (zc:z∈s.cliquePart) :
    let Y := insert z s.singles
    2*matchingEdges (Q.induce Yᶜ)=D := by
  intro Y
  have zs : z∉s.singles := fun hs => Set.disjoint_left.mp s.dis hs zc
  have size : Y.ncard=I.ncard := (Set.ncard_insert_of_notMem zs).trans s.count
  have yi : Q.IsIndepSet Y := by
    intro a ha b hb ne edge
    rcases ha with az|as_ <;> rcases hb with bz|bs
    · exact ne (az.trans bz.symm)
    · rcases s.singleEdges b bs a edge.symm with ai|aa
      · exact s.cOut zc (az ▸ ai)
      · exact s.ac ((az.symm.trans aa) ▸ zc)
    · rcases s.singleEdges a as_ b edge with bi|ba
      · exact s.cOut zc (bz ▸ bi)
      · exact s.ac ((bz.symm.trans ba) ▸ zc)
    · rcases s.singleEdges a as_ b edge with bi|ba
      · exact s.sOut bs bi
      · exact s.as_ (ba ▸ bs)
  have rank := (zero_reserve_independent_cut Q D (by omega) reg crit zero Y ⟨z,Or.inl rfl⟩ yi).2.1
  have ord := factorCritical_order_rank Q crit z
  have host := heavy_clique_host_order Q I D s
  omega

#print axioms even_clique_and_edge_family_rank
#print axioms independent_cut_leaves_half_rank
end JSP452Audit.StarHost
