import FiveDegreeSelectorCeiling
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- One original edge leaves each full-degree vertex missed by the same
optimal maximum matching. Its other endpoint is allowed to serve many labels. -/
structure FiveExposurePorts (G : SimpleGraph X) where
  M : G.Subgraph
  matching : M.IsMatching
  maximum : M.edgeSet.ncard=matchingEdges G
  U : Set X
  exposed : U=exposedFull G M 5
  count : U.ncard=minimumExposure G 5
  target : U→X
  link : ∀u,G.Adj u.val (target u)
  targetMatched : ∀u,target u∈M.verts

theorem five_exposure_ports_exist (G : SimpleGraph X) : Nonempty (FiveExposurePorts G) := by
  classical
  obtain ⟨M,hm,max,optimal⟩ := minimumExposure_attained G 5
  let U := exposedFull G M 5
  have chooseTarget (u:U) : ∃w,G.Adj u.val w ∧ w∈M.verts := by
    have five : (G.neighborSet u.val).ncard=5 := (Nat.card_coe_set_eq _).symm.trans u.property.2
    obtain ⟨w,edge⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<(G.neighborSet u.val).ncard by omega)
    refine ⟨w,edge,?_⟩
    by_contra away
    let E := G.subgraphOfAdj edge
    have dis : Disjoint M.verts E.verts := by
      apply Set.disjoint_left.mpr
      rintro x old (eq|eq)
      · exact u.property.1 (eq ▸ old)
      · exact away ((Set.mem_singleton_iff.mp eq) ▸ old)
    have bigger := JSP452Audit.Padded.matching_sup_of_disjoint_verts G hm (Subgraph.IsMatching.subgraphOfAdj edge) dis
    have strict : M.verts ⊂ (M⊔E).verts :=
      ⟨fun _ h => Or.inl h,fun reverse => u.property.1 (reverse (Or.inr (Or.inl rfl)))⟩
    have inc := Set.ncard_lt_ncard strict
    rw [matching_vertices_eq_twice_edges bigger,matching_vertices_eq_twice_edges hm,max] at inc
    have bound := le_matchingEdges bigger
    omega
  choose target link hit using chooseTarget
  exact ⟨⟨M,hm,max,U,rfl,optimal,target,link,hit⟩⟩

namespace FiveExposurePorts
variable {G : SimpleGraph X} (s : FiveExposurePorts G)

theorem missed (u:s.U) : u.val∉s.M.verts := by
  have h : u.val∈exposedFull G s.M 5 := by rw [←s.exposed];exact u.property
  exact h.1
theorem off (u:s.U) : s.target u∉s.U := by
  intro inside
  exact (show s.target u∈exposedFull G s.M 5 from s.exposed ▸ inside).1 (s.targetMatched u)

def chosenAt (A : Set s.U) (x y:X) : Prop :=
  ∃u∈A,(u.val=x ∧ s.target u=y) ∨ (u.val=y ∧ s.target u=x)

theorem chosen_symm (A : Set s.U) (x y:X) : s.chosenAt A x y → s.chosenAt A y x := by
  rintro ⟨u,hu,h⟩
  exact ⟨u,hu,h.symm⟩

def kept (x y:X) : Prop := G.Adj x y ∧ ¬s.M.Adj x y ∧ ¬s.chosenAt Set.univ x y

def portAt {Z : Type*} (x:X) : s.U⊕Z → Prop := Sum.elim (fun u => s.target u=x) (fun _ => False)

def auxiliary {Z : Type*} (J : SimpleGraph (s.U⊕Z)) : SimpleGraph (X⊕(s.U⊕Z)) where
  Adj
    | .inl x,.inl y => s.kept x y
    | .inl x,.inr y => s.portAt x y
    | .inr y,.inl x => s.portAt x y
    | .inr a,.inr b => J.Adj a b
  symm := by
    constructor
    rintro (x|x) (y|y) h
    · exact ⟨h.1.symm,fun m => h.2.1 m.symm,fun t => h.2.2 (s.chosen_symm _ _ _ t)⟩
    · cases y <;> exact h
    · cases x <;> exact h
    · exact h.symm
  loopless := by
    constructor
    rintro (x|y) h
    · exact G.irrefl h.1
    · exact J.irrefl h

end FiveExposurePorts
#print axioms five_exposure_ports_exist
#print axioms FiveExposurePorts.auxiliary
end JSP452Audit.StarHost
