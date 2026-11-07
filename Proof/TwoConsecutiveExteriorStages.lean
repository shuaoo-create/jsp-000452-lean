import ActualEightExteriorDeficit
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

theorem two_stage_exact_prefix {X:Type*} [Finite X] (G:SimpleGraph X) (d:ℕ)
    (B:Set X) (first:CompleteDegreeStage G (d+1) B) (C:Set ↥(Bᶜ:Set X)) (second:CompleteDegreeStage (G.induce Bᶜ) d C)
    (k:ℕ) (fit:k≤B.ncard+C.ncard) :
    ∃V:Set X,V.ncard=k ∧ G.edgeSet.ncard=(G.induce Vᶜ).edgeSet.ncard+d*k+min k B.ncard := by
  by_cases left:k≤B.ncard
  · obtain ⟨V,_,size,cost⟩ := subset_of_stage_price G (d+1) B first k left
    refine ⟨V,size,?_⟩
    rw [min_eq_left left,add_mul,one_mul] at *;omega
  · obtain ⟨V,_,size,cost⟩ := subset_of_stage_price (G.induce Bᶜ) d C second (k-B.ncard) (by omega)
    have original := JSP452Audit.StarHost.degree_on_independent_full_set G B (d+1) first.2.1 first.1
    have final := nested_deletion_edges G B V
    have card := nested_removed_card B V
    refine ⟨nestedRemoved B V,by omega,?_⟩
    have eq : d*k=d*(k-B.ncard)+d*B.ncard := by rw [←Nat.mul_add];congr 1;omega
    rw [add_mul,one_mul] at original
    rw [eq,min_eq_right (by omega : B.ncard≤k)]
    omega

theorem conservative_whole_menu_row {I X:Type*} [Fintype I] [DecidableEq I] [Finite X]
    (G:SimpleGraph X) (e:I↪G.ConnectedComponent) (V:Set X) (z:I→ℕ) {s t r:ℕ} (n m:ℕ→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (upper:∀i,matchingEdges (e i).toSimpleGraph≤z i)
    (menu:SplitCapacities z (r+V.ncard)) (row:ForcingRow G s t n m r) :
    let H := Finset.univ.sup (fun i => labelledPart G (e i))
    ForcingRow ((G \ H).induce Vᶜ) s t n m (r+V.ncard+∑i,z i) := by
  apply actual_piece_menu_of_splits G V (fun i => labelledPart G (e i)) z n m hn hm pn pm (fun _ _ _ edge => edge.1) _ menu row
  intro T
  exact (original_component_menu_accounts G e T).1.le.trans (Finset.sum_le_sum (fun i _ => upper i))

#print axioms two_stage_exact_prefix
#print axioms conservative_whole_menu_row
end JSP452Audit.StarHost
