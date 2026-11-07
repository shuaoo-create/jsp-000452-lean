import TrueIncidenceMatchingsCountCoveredCoresAndCoveredRoots
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]

theorem named_port_matching {I:Type*} [Finite I] (L:R→C→Prop) (a:I↪R) (c:I↪C) (edge:∀i,L (a i) (c i)) :
    ∃M:(portIncidenceGraph L).Subgraph,M.IsMatching ∧ M.edgeSet.ncard=Nat.card I ∧ ∀i,Sum.inl (a i)∈M.verts := by
  let l : I↪R⊕C := ⟨fun i => Sum.inl (a i),fun _ _ eq => a.injective (Sum.inl.inj eq)⟩
  let r : I↪R⊕C := ⟨fun i => Sum.inr (c i),fun _ _ eq => c.injective (Sum.inr.inj eq)⟩
  have link (i) : (portIncidenceGraph L).Adj (l i) (r i) := edge i
  have dis : Disjoint (Set.range l) (Set.range r) := Set.disjoint_left.mpr (by
    rintro _ ⟨i,rfl⟩ ⟨j,e⟩;cases e)
  let M := pairFamily (portIncidenceGraph L) l r link
  have hm : M.IsMatching := pairFamily_isMatching _ l r link dis
  have size := matching_vertices_eq_twice_edges hm
  change (Set.range l∪Set.range r).ncard=2*M.edgeSet.ncard at size
  rw [Set.ncard_union_eq dis,Set.ncard_range_of_injective l.injective,Set.ncard_range_of_injective r.injective] at size
  exact ⟨M,hm,by omega,fun i => Or.inl ⟨i,rfl⟩⟩

theorem port_rank_plus_hall_deficit (L:R→C→Prop) :
    Nat.card C≤matchingEdges (portIncidenceGraph L)+classDeficiency L Set.univ := by
  classical
  let d := classDeficiency L Set.univ
  obtain ⟨f,ok⟩ := all_cores_with_dummy_slots L Set.univ
  let label (c:C) : R⊕Fin d := f ⟨c,Set.mem_univ c⟩
  have inject : Function.Injective label := fun _ _ e => congrArg Subtype.val (f.injective e)
  let good : Set C := {c|∃r,label c=.inl r}
  let root (c:good) := c.property.choose
  have named (c:good) : label c.val=.inl (root c) := c.property.choose_spec
  have ri : Function.Injective root := fun i j e => Subtype.ext (inject ((named i).trans ((congrArg Sum.inl e).trans (named j).symm)))
  have link (c:good) : L (root c) c.val := ok ⟨c.val,Set.mem_univ _⟩ _ (named c)
  obtain ⟨M,hm,count,_⟩ := named_port_matching L ⟨root,ri⟩ (Function.Embedding.subtype (·∈good)) link
  have fake (c:↥(goodᶜ:Set C)) : ∃i:Fin d,label c.val=.inr i := by
    cases e:label c.val with
    | inl r => exact (c.property ⟨r,e⟩).elim
    | inr i => exact ⟨i,rfl⟩
  choose which eq using fake
  have inj : Function.Injective which := fun i j e => Subtype.ext (inject ((eq i).trans ((congrArg Sum.inr e).trans (eq j).symm)))
  have unused := Nat.card_le_card_of_injective which inj
  rw [Nat.card_fin,Nat.card_coe_set_eq] at unused
  rw [Nat.card_coe_set_eq] at count
  have all := Set.ncard_add_ncard_compl good
  have limit := le_matchingEdges hm
  change Nat.card C≤matchingEdges (portIncidenceGraph L)+d;omega

theorem optimal_incidence_assignment_with_required_roots (L:R→C→Prop) (A:Set R)
    (seed:↥A↪C) (legal:∀a,L a.val (seed a)) :
    let d := classDeficiency L Set.univ
    ∃M:(portIncidenceGraph L).Subgraph,M.IsMatching ∧ M.edgeSet.ncard=matchingEdges (portIncidenceGraph L) ∧
      A⊆PortMatching.roots M ∧ ((PortMatching.cores M)ᶜ:Set C).ncard≤d := by
  intro d
  obtain ⟨P,hm,_,covers⟩ := named_port_matching L (Function.Embedding.subtype (·∈A)) seed legal
  obtain ⟨M,matchM,opt,keep⟩ := exists_maximum_matching_covering _ P hm
  have budget := port_rank_plus_hall_deficit L
  change Nat.card C≤matchingEdges (portIncidenceGraph L)+d at budget
  have eq := (PortMatching.matched_endpoint_counts matchM).1
  have all := Set.ncard_add_ncard_compl (PortMatching.cores M)
  exact ⟨M,matchM,opt,fun r h => keep (covers ⟨r,h⟩),by omega⟩

#print axioms named_port_matching
#print axioms port_rank_plus_hall_deficit
#print axioms optimal_incidence_assignment_with_required_roots
end JSP452Audit.StarHost
