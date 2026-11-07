import TheTwoRemainingGapsShareTheSameCertifiedRootCredit
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_degree_has_no_odd_regular_component {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ) (odd:Odd D) :
    (oddRegularComponents G D).ncard=0 := by
  have empty : oddRegularComponents G D=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro Q mem
    have sum := JSP452Audit.StarHost.two_block_handshake G Q.supp
    have closed : crossCount G Q.supp Q.suppᶜ=0 := crossCount_of_no_edges G _ _ (fun x hx y hy e => hy ((Q.mem_supp_congr_adj e).mp hx))
    rw [closed,Nat.add_zero,degree_sum_full G Q.supp D mem.2] at sum
    have order := mem.1
    rw [Nat.card_coe_set_eq] at order
    have parity := odd.mul order
    rw [sum,Nat.odd_iff] at parity;omega
  simp [empty]

theorem gap_two_top_typed (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let N := P.paidCore.ncard
    let e := minimumExposure (F.G.induce P.paidCore) D
    D=H+2 → e≤P.excess ∧ (D%2=1 → e=0) ∧
      (∀x y,WinsHeight F.n F.m r D x y → 3≤min x y ∧ ExactTypedWidth Y x y (widthAt F.n F.m r D-N/4-e)) ∧
      widthAt F.n F.m r D≤uniformEnvelope Y D+N/4+e ∧ widthAt F.n F.m r D≤peakCountAbove Y (D-2)+N/4+e := by
  intro D H r Y N e gap
  let C := F.G.induce P.paidCore
  let W := widthAt F.n F.m r D
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have sum := (strict_double_head_gap_range F paid).2.1
  change D+2≤F.n ⟨0,F.hs⟩+F.m ⟨0,F.ht⟩ at sum
  have debt : e≤(oddRegularComponents F.G D).ncard := (P.true_internal_hole_budget cap).trans P.genuine_regular_injection
  refine ⟨debt.trans (P.includes_odd_regular_excess kl E),fun odd => Nat.eq_zero_of_le_zero (debt.trans_eq
    (odd_degree_has_no_odd_regular_component F.G D (Nat.odd_iff.mpr odd))),?_⟩
  have prices (x y:ℕ) (win:WinsHeight F.n F.m r D x y) : 3≤min x y ∧ ExactTypedWidth Y x y (W-N/4-e) := by
    have a : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
    have b : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
    have ht := win.2.2.1
    have minH : 3≤min x y := by omega
    have bound : N/(min x y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
    have prior : (∃p,p<F.n ⟨0,F.hs⟩ ∧ D=p+(y-1)) ∨ (∃q,q<F.m ⟨0,F.ht⟩ ∧ D=q+(x-1)) := by
      by_cases red:x<F.n ⟨0,F.hs⟩
      · exact Or.inl ⟨x,red,by omega⟩
      · exact Or.inr ⟨y,by omega,by omega⟩
    have seen := near_top_two_sided_recovery Y C F.n F.m F.hs F.ht F.hn F.hm (strict_payable_exterior_constraints F paid P).2.2.2.2.2
      win (show 0<D by omega) (fun v => (induced_neighbor_count_le F.G _ v).trans (cap v.val)) prior
    rw [Nat.card_coe_set_eq] at seen
    change ExactTypedWidth Y x y (W-N/(min x y+1)-e) at seen
    exact ⟨minH,actual_typed_width_down _ seen (by omega)⟩
  refine ⟨prices,?_⟩
  by_cases active:0<W
  · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D by omega) active
    have win : WinsHeight F.n F.m r D x y := w
    have typed := (prices x y win).2
    have env : W-N/4-e≤uniformEnvelope Y D := by
      rcases typed with zero|⟨u,v,hu,hv,len,force⟩
      · omega
      · exact len ▸ uniform_pair_le_envelope Y x y u v D win.1 win.2.1 hu hv win.2.2.1 force
    obtain ⟨sz,lo⟩ := exact_peak_inventory_cut Y (D-2)
    have ht := win.2.2.1
    have inv := typed_inventory_on_actual_cut Y win.1 win.2.1 (by omega : x+y-1=(D-1)+1) (by omega)
      typed _ (fun z => (lo z).trans_lt (by omega))
    rw [sz] at inv
    change W≤_ ∧ W≤_;omega
  · change W≤_ ∧ W≤_;omega

#print axioms odd_degree_has_no_odd_regular_component
#print axioms gap_two_top_typed
end JSP452Audit.StarHost
