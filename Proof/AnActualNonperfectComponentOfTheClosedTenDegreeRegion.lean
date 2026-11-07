import TenDegreeClosedFourOrTheActualScoreOneCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ClosedTenFour.actual_imperfect_component {X:Type u} [Finite X] {G:SimpleGraph X} (C:ClosedTenFour G)
    (none:(oddRegularComponents G 10).ncard=0) :
    ∃c:G.ConnectedComponent,c.supp⊆C.support ∧ (∀x∈c.supp,Nat.card (G.neighborSet x)=10) ∧
      (Nat.card c.supp=2*matchingEdges c.toSimpleGraph+2 ∨ Nat.card c.supp=2*matchingEdges c.toSimpleGraph+4) := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  let T := Finset.univ.filter (fun c:G.ConnectedComponent => c.supp⊆C.support)
  have eq : componentVertices G T=C.support := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp (show G.connectedComponentMk x∈T from hx)).2 (show x∈(G.connectedComponentMk x).supp from rfl)
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cubic_closed_component G C.support x hx C.closed⟩
  obtain ⟨size,rank,_⟩ := component_union_accounts G T
  change (componentVertices G T).ncard=_ at size
  change matchingEdges (G.induce (componentVertices G T))=_ at rank
  rw [eq] at size rank
  let delta (c:G.ConnectedComponent) := Nat.card c.supp-2*matchingEdges c.toSimpleGraph
  have each (c:G.ConnectedComponent) : Nat.card c.supp=2*matchingEdges c.toSimpleGraph+delta c := by
    have lim := matching_edges_fit_order c.toSimpleGraph
    change 2*matchingEdges c.toSimpleGraph≤Nat.card c.supp at lim
    dsimp only [delta];omega
  have total := Finset.sum_congr (s₁:=T) rfl (fun c _ => each c)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←size,←rank] at total
  have four := C.deficit
  have some : ∃c∈T,0<delta c := by
    by_contra! n
    have zero := Finset.sum_eq_zero (s:=T) (fun c hc => Nat.eq_zero_of_le_zero (n c hc))
    omega
  obtain ⟨c,mem,pos⟩ := some
  have limit := Finset.single_le_sum (f:=delta) (fun _ _ => Nat.zero_le _) mem
  have sub := (Finset.mem_filter.mp mem).2
  have full (x) (hx:x∈c.supp) := C.full x (sub hx)
  have even : Even (Nat.card c.supp) := by
    by_contra h
    have member : c∈oddRegularComponents G 10 := ⟨Nat.not_even_iff_odd.mp h,full⟩
    have nn := (Set.ncard_pos (Set.toFinite _)).mpr (show (oddRegularComponents G 10).Nonempty from ⟨c,member⟩)
    omega
  have actual := each c
  obtain ⟨k,evenK⟩ := even
  exact ⟨c,sub,full,by omega⟩

#print axioms ClosedTenFour.actual_imperfect_component
end JSP452Audit.StarHost
