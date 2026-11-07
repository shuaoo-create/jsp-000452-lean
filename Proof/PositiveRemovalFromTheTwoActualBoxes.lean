import TheActualBoxBudgetRowOutsideTheRoots
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem box_union_has_nine_vertex_component (cap : ∀v,Nat.card (G.neighborSet v)≤9) :
    ∃c : (G.induce R.chosen).ConnectedComponent,9≤Nat.card c.supp := by
  let C := G.induce R.chosen
  have mass := (R.region_rank_edges cap).2.1
  have order := R.chosen_structure.1
  have ha := (R.inner 0).2
  change 5≤R.capacity 0 at ha
  have positive : 0<R.totalCapacity := by change 0<R.capacity 0+R.capacity 1;omega
  have high : ∃v,9≤Nat.card (C.neighborSet v) := by
    by_contra! low
    let V : Set (↥R.chosen) := Set.univ
    have bound := degree_sum_le_cap C V 8 (fun x _ => by have := low x;omega)
    have sum := degree_sum_complement C V
    have empty : originalDegreeSum C Vᶜ=0 := by simp [V,originalDegreeSum]
    rw [empty,Nat.add_zero] at sum
    change (G.induce R.chosen).edgeSet.ncard=9*R.totalCapacity+8 at mass
    change originalDegreeSum C V=2*(G.induce R.chosen).edgeSet.ncard at sum
    rw [show V.ncard=R.chosen.ncard from Set.ncard_univ (↥R.chosen)] at bound
    omega
  obtain ⟨v,hits⟩ := high
  let c := C.connectedComponentMk v
  have across : C.neighborSet v⊆c.supp := by
    intro y edge
    exact (c.mem_supp_congr_adj edge).mp (show v∈c.supp by rfl)
  have bound := Set.ncard_le_ncard across
  exact ⟨c,by change 9≤c.supp.ncard;change 9≤(C.neighborSet v).ncard at hits;omega⟩

theorem port_budget_loss_limits {s : ℕ} (hs : 0<s) (n : Fin s→ℕ) (small : ∀i,n i≤8)
    (cap : ∀v,Nat.card (G.neighborSet v)≤9) :
    1≤(componentBudget (G.induce R.chosen) n).loss ∧
      (componentBudget (G.induce R.chosen) n).loss≤R.totalCapacity := by
  let C := G.induce R.chosen
  obtain ⟨c,order⟩ := R.box_union_has_nine_vertex_component cap
  have rank := (R.region_rank_edges cap).1
  have fit := component_budget_loss_le C n
  have pos := (R.inner 0).2
  change 5≤R.capacity 0 at pos
  have big : 0<R.totalCapacity := by change 0<R.capacity 0+R.capacity 1;omega
  let i : Fin s := ⟨0,hs⟩
  have pay := component_budget_accepts_singleton C n i c (by change 0<matchingEdges (G.induce R.chosen);omega)
    (by have := small i;omega)
  change matchingEdges C=R.totalCapacity at rank
  exact ⟨pay,fit.trans rank.le⟩

#print axioms box_union_has_nine_vertex_component
#print axioms port_budget_loss_limits
end JSP452Audit.StarHost.NinePortRegion
