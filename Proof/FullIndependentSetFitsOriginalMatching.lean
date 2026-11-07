import QuantitativeExposureOnSmallerRows
namespace JSP452Audit.StarHost
open SimpleGraph

theorem full_independent_set_le_matching {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (pos:0<D)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (I:Set X) (ind:G.IsIndepSet I)
    (full:∀v∈I,Nat.card (G.neighborSet v)=D) : I.ncard≤matchingEdges G := by
  classical
  let H : SimpleGraph X := {
    Adj := fun x y => G.Adj x y ∧ (x∈I ↔ y∉I)
    symm := ⟨fun _ _ e => ⟨e.1.symm,by have := e.2;tauto⟩⟩
    loopless := ⟨fun _ e => G.irrefl e.1⟩ }
  have sub : H≤G := fun _ _ e => e.1
  have same (x) (hx:x∈I) : H.neighborSet x=G.neighborSet x := by
    ext y
    exact ⟨fun e => e.1,fun e => ⟨e,iff_of_true hx (fun hy => ind hx hy e.ne e)⟩⟩
  obtain ⟨M,matchM,covered⟩ := bipartite_full_degree_matching H I D pos
    (fun v => (Set.ncard_le_ncard (show H.neighborSet v⊆G.neighborSet v from fun _ h => sub h)).trans (cap v)) (fun _ _ e => e.2)
  have hit (x) (hx:x∈I) : x∈M.verts := covered x (by rw [same x hx];exact full x hx)
  have partner (x:↥I) : ∃y,M.Adj x.val y := by obtain ⟨y,e,_⟩ := matchM (hit x.val x.property);exact ⟨y,e⟩
  choose mate edge using partner
  have inj : Function.Injective mate := by
    intro x y eq
    apply Subtype.ext
    exact matchM.eq_of_adj_left (edge x).symm (eq.symm ▸ (edge y).symm)
  have apart : Disjoint I (Set.range mate) := Set.disjoint_left.mpr (by
    rintro y hy ⟨x,rfl⟩;exact ((M.adj_sub (edge x)).2.mp x.property) hy)
  have inc : I∪Set.range mate⊆M.verts := by
    rintro y (hy|⟨x,rfl⟩);exact hit y hy;exact M.edge_vert (edge x).symm
  have count := Set.ncard_le_ncard inc
  rw [Set.ncard_union_eq apart,Set.ncard_range_of_injective inj,matching_vertices_eq_twice_edges matchM] at count
  change I.ncard+I.ncard≤2*M.edgeSet.ncard at count
  exact (show I.ncard≤M.edgeSet.ncard by omega).trans ((le_matchingEdges matchM).trans (rank_le_of_copy (SimpleGraph.Copy.ofLE H G sub)))

#print axioms full_independent_set_le_matching
end JSP452Audit.StarHost
