import LengthDichotomyOnActualBoxes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem endpoint_forest_vertex_budget {X:Type*} [Finite X] {s q:ℕ}
    (G:SimpleGraph X) (n:Fin s→ℕ) (pn:∀i,1≤n i) (ep:ForestMatchingEndpoint G n q)
    (pos:0<q) (fits:q≤matchingEdges G) : s+(∑i,n i)+(q-1)≤Nat.card X := by
  have rank := matching_edges_fit_order G
  have le : q-1≤(Set.univ:Set X).ncard := by rw [Set.ncard_univ];omega
  obtain ⟨A,_,card⟩ := Set.exists_subset_card_eq le
  obtain ⟨f⟩ := endpoint_survives_cover G n pn ep A (by omega)
  have count := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σi:Fin s,Fin (n i+1))≤Aᶜ.ncard at count
  rw [Nat.card_sigma] at count
  simp only [Nat.card_fin,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at count
  have total := Set.ncard_add_ncard_compl A
  omega

theorem strict_nine_short_box_masses (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    (F.s≤P → (∑i,F.n i)+d≤P+2) ∧ (F.t≤P → (∑j,F.m j)+d≤P+2) := by
  intro P d
  let C := F.G.induce R.chosen
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have rank : matchingEdges C=P := (R.region_rank_edges cap).1
  obtain ⟨red,blue⟩ := strict_nine_short_box_endpoint F paid nine R
  have size := R.chosen_structure.1
  change R.chosen.ncard=2*P+2 at size
  constructor
  · intro le
    obtain ⟨ep,fit,_⟩ := red le
    have spend := endpoint_forest_vertex_budget C F.n F.pn ep (by omega) (rank.symm ▸ fit)
    change F.s+(∑i,F.n i)+(P-F.s+d+1-1)≤R.chosen.ncard at spend;omega
  · intro le
    obtain ⟨ep,fit,_⟩ := blue le
    have spend := endpoint_forest_vertex_budget C F.m F.pm ep (by omega) (rank.symm ▸ fit)
    change F.t+(∑i,F.m i)+(P-F.t+d+1-1)≤R.chosen.ncard at spend;omega

#print axioms endpoint_forest_vertex_budget
#print axioms strict_nine_short_box_masses
end JSP452Audit.StarHost
