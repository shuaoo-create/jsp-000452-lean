import NineOriginalListsAvoidTheCapacityWindow
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_live_head_requires_vertices (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : NinePortRegion F.G) (p : ℕ) (T : Set F.X)
    (cap : ∀v : ↥(Tᶜ : Set F.X),Nat.card ((R.erased.induce Tᶜ).neighborSet v)≤p) :
    let d := F.rank-matchingEdges F.G
    (R.totalCapacity<F.t → 0<originalThresholdCount F.n (p+1) →
      2*(d+∑i,(F.n i-1)/2)+originalThresholdCount F.n (p+1)≤T.ncard+1) ∧
    (R.totalCapacity<F.s → 0<originalThresholdCount F.m (p+1) →
      2*(d+∑j,(F.m j-1)/2)+originalThresholdCount F.m (p+1)≤T.ncard+1) := by
  intro d
  have below := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp only [d];omega
  obtain ⟨red,blue⟩ := strict_nine_actual_erased_endpoints F paid R
  constructor
  · intro long live
    obtain ⟨hq,_,account,ep,_⟩ := red long
    exact endpoint_stage_inventory R.erased F.hs F.n F.pn ep pos (by omega) account T cap live
  · intro long live
    obtain ⟨hq,_,account,ep,_⟩ := blue long
    exact endpoint_stage_inventory R.erased F.ht F.m F.pm ep pos (by omega) account T cap live

theorem nine_erased_degree_cap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (v : F.X) :
    Nat.card (R.erased.neighborSet v)≤9 := by
  have sub : R.erased.neighborSet v⊆F.G.neighborSet v := fun _ h => h.1
  exact (Set.ncard_le_ncard sub).trans (((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine)

/-- Both long lists together force at least 2d+6 deleted labels before the
cap can fall below seven. The preceding endpoint bound also applies with just one long list. -/
theorem strict_nine_cost_to_drop_below_seven (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (T : Set F.X)
    (cap : ∀v : ↥(Tᶜ : Set F.X),Nat.card ((R.erased.induce Tᶜ).neighborSet v)≤6)
    (both : R.totalCapacity<min F.s F.t) :
    2*(F.rank-matchingEdges F.G)+6≤T.ncard := by
  obtain ⟨_,_,_,_,i,j,_,_,_,peaks,_⟩ := strict_nine_original_peak F paid nine
  have prices := strict_nine_live_head_requires_vertices F paid R 6 T cap
  rcases peaks with ⟨_,blue⟩|⟨red,_⟩
  · have head := (original_threshold_prefix F.m F.hm 7 j).mp (by omega)
    have live : 0<originalThresholdCount F.m (6+1) := Nat.zero_lt_of_lt head
    have price := prices.2 (lt_min_iff.mp both).1 live
    have hits := Finset.single_le_sum (f:=fun v => (F.m v-1)/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  · have head := (original_threshold_prefix F.n F.hn 7 i).mp (by omega)
    have live : 0<originalThresholdCount F.n (6+1) := Nat.zero_lt_of_lt head
    have price := prices.1 (lt_min_iff.mp both).2 live
    have hits := Finset.single_le_sum (f:=fun v => (F.n v-1)/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

#print axioms strict_nine_live_head_requires_vertices
#print axioms nine_erased_degree_cap
#print axioms strict_nine_cost_to_drop_below_seven
end JSP452Audit.StarHost
