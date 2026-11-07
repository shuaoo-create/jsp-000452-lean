import TheActualRegularBlockItsHalfOrderAndItsOppositeExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] (G:SimpleGraph X)

theorem complete_stage_of_exact_deletion (D:ℕ) (U:Set X) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (charge:G.edgeSet.ncard=(G.induce Uᶜ).edgeSet.ncard+D*U.ncard)
    (low:∀v:↥(Uᶜ:Set X),Nat.card ((G.induce Uᶜ).neighborSet v)<D) : CompleteDegreeStage G D U := by
  classical
  have exact := root_deletion_cost G U
  have max := degree_sum_le_cap G U D (fun x _ => cap x)
  have empty : (G.induce U).edgeSet=∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)
  have ind : G.IsIndepSet U := by
    intro a ha b hb _ e
    have edge : s(⟨a,ha⟩,⟨b,hb⟩)∈(G.induce U).edgeSet := e
    rw [empty] at edge;exact edge
  have full (v:X) (hv:v∈U) : Nat.card (G.neighborSet v)=D := by
    by_contra! ne
    have less : Nat.card (G.neighborSet v)<D := lt_of_le_of_ne (cap v) ne
    let A := U.toFinite.toFinset
    have size : A.card=U.ncard := by rw [←Set.ncard_coe_finset,Set.Finite.coe_toFinset]
    have bound := Finset.sum_lt_sum (s:=A) (g:=fun _ => D) (f:=fun w => Nat.card (G.neighborSet w))
      (fun w _ => cap w) ⟨v,(U.toFinite.mem_toFinset.mpr hv),less⟩
    change originalDegreeSum G U<(∑_w∈A,D) at bound
    simp only [Finset.sum_const,size,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm U.ncard D] at bound
    omega
  refine ⟨ind,full,?_⟩
  intro v atD
  by_cases inside:v∈U
  · exact Or.inl inside
  · right;by_contra! missing
    let x : ↥(Uᶜ:Set X) := ⟨v,inside⟩
    have subset : G.neighborSet v⊆Uᶜ := fun w adj cut => missing w cut adj
    have eq : Nat.card ((G.induce Uᶜ).neighborSet x)=D := by
      rw [induced_degree_intersection,Set.inter_eq_left.mpr subset]
      exact (Nat.card_coe_set_eq _).symm.trans atD
    have := low x;omega

theorem history_equal_fee_interval (s t d:ℕ) (order:s≤t) (fixed:∀j,s≤j → j<t → peakFee G j=d) :
    (G.induce (peakPrefix G s)ᶜ).edgeSet.ncard=(G.induce (peakPrefix G t)ᶜ).edgeSet.ncard+d*(t-s) := by
  have later := peak_prefix_edge_account G t
  have early := peak_prefix_edge_account G s
  let u := t-s
  have all := Finset.sum_range_add (peakFee G) s u
  have count : (∑j∈Finset.range u,peakFee G (s+j))=d*u := by
    calc
      _ = ∑_j∈Finset.range u,d := Finset.sum_congr rfl (fun j hj => fixed (s+j) (by omega) (by have := Finset.mem_range.mp hj;dsimp only [u] at this;omega))
      _ = _ := by simp [Nat.mul_comm]
  rw [show s+u=t by dsimp only [u];omega,count] at all
  change _=_+d*u
  omega

theorem peak_history_complete_top_stage (D:ℕ) (pos:0<D) (cap:∀v,Nat.card (G.neighborSet v)≤D) :
    let b := peakCountAbove G (D-1)
    let U := peakPrefix G b
    CompleteDegreeStage G D U ∧ U.ncard=b := by
  intro b U
  obtain ⟨size,low⟩ := exact_peak_inventory_cut G (D-1)
  have charge : (G.induce (peakPrefix G 0)ᶜ).edgeSet.ncard=(G.induce Uᶜ).edgeSet.ncard+D*(b-0) :=
    history_equal_fee_interval G 0 b D (Nat.zero_le _) (fun j _ before => by
      have high := ((peak_inventory_spec G (D-1)).2.2 j).1 before
      rcases (chosenPeakStep G (peakPrefix G j)).attained with zero|⟨v,real⟩
      · change peakFee G j=0 at zero;omega
      · have up := (induced_neighbor_count_le G _ v).trans (cap v.val)
        change Nat.card ((G.induce (peakPrefix G j)ᶜ).neighborSet v)=peakFee G j at real;omega)
  have base := peak_prefix_edge_account G 0
  simp only [Finset.range_zero,Finset.sum_empty,Nat.add_zero] at base
  refine ⟨complete_stage_of_exact_deletion G D U cap ?_ (fun x => (low x).trans_lt (by omega)),size⟩
  rw [base,size];simpa only [Nat.sub_zero] using charge

#print axioms complete_stage_of_exact_deletion
#print axioms history_equal_fee_interval
#print axioms peak_history_complete_top_stage
end JSP452Audit.StarHost
