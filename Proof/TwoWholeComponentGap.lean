import SixWholeComponentExactDeletion
namespace JSP452Audit.StarHost
open SimpleGraph

theorem two_capacity_splits (z:Fin 2→ℕ) (r:ℕ) (ord:z 0≤z 1)
    (small:z 0≤r+1) (gap:z 1-z 0≤r+1) : SplitCapacities z r := by
  intro i j total
  rw [Fin.sum_univ_two] at total
  have legal (T:Finset (Fin 2)) (a:ℕ) (price:(∑k∈T,z k)=a) (fit:a≤ i) (other:z 0+z 1≤a+j) :
      ∃U:Finset (Fin 2),(∑k∈U,z k)≤ i ∧ (∑k∈Uᶜ,z k)≤j := by
    have split := Finset.sum_add_sum_compl T z
    rw [Fin.sum_univ_two,price] at split
    exact ⟨T,price ▸ fit,by omega⟩
  by_cases first : i<z 0
  · exact legal ∅ 0 (by simp) (by omega) (by omega)
  by_cases second : i<z 1
  · exact legal {0} (z 0) (by simp) (by omega) (by omega)
  by_cases whole : i<z 0+z 1
  · exact legal {1} (z 1) (by simp) (by omega) (by omega)
  exact legal Finset.univ (z 0+z 1) (by rw [Fin.sum_univ_two]) (by omega) (by omega)

theorem strict_pair_gap_needs_paid_exterior {F:StrictFamily.{u}} (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (e:Fin 2 ↪ F.G.ConnectedComponent)
    (actual:∀i,e i∈oddRegularComponents F.G 6) (V:Set F.X)
    (ind:F.G.IsIndepSet V) (full:∀v∈V,Nat.card (F.G.neighborSet v)=6)
    (away:∀i,Disjoint (e i).supp V)
    (ord:matchingEdges (e 0).toSimpleGraph≤matchingEdges (e 1).toSimpleGraph) :
    let a := matchingEdges (e 0).toSimpleGraph
    let b := matchingEdges (e 1).toSimpleGraph
    F.r+V.ncard+1<max a (b-a) := by
  intro a b
  by_contra! low
  have menu := two_capacity_splits (fun i => matchingEdges (e i).toSimpleGraph) (F.r+V.ncard) ord
    ((Nat.le_max_left a (b-a)).trans low) ((Nat.le_max_right a (b-a)).trans low)
  have impossible := strict_six_no_full_degree_menu F paid six e actual V menu ind full away
  rw [Fintype.card_fin] at impossible
  obtain ⟨K⟩ := degreeRegion_exists F.G 6
  obtain ⟨_,hc,cr,lim,_⟩ := strict_six_four_exposure_entry F paid six K
  omega

#print axioms two_capacity_splits
#print axioms strict_pair_gap_needs_paid_exterior
end JSP452Audit.StarHost
