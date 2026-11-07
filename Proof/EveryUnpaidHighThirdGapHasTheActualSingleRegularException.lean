import DecideTheRealThirdGapHighPlatformPricesAndBothCapParities
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 800000 in
theorem third_gap_high_is_single (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let r := F.r+P.cutRoots.ncard
    0<h → h≤P.excess → 8*P.gamma h+(3*(D:ℤ)+2)*P.excess+((D:ℤ)-10)*h+4*P.beta≤0 →
    (D=11 → 8*P.gamma h+(3*(D:ℤ)+5)*P.excess+((D:ℤ)-9)*h+4*P.beta≤0) →
    D=H+3 → P.capacity<widthAt F.n F.m r (D-1) → P.excess=1 := by
  intro D H h r hp rp signed odd gap high
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 8≤H := by omega
  have credit : P.gamma h≤0 := by
    have a := mul_nonneg (show (0:ℤ)≤3*(D:ℤ)+2 by omega) (show (0:ℤ)≤P.excess by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤h by positivity)
    omega
  let C := F.G.induce P.paidCore
  let Y := F.G.induce P.exterior
  let Z := P.capacity
  let N := P.paidCore.ncard
  let c₀ := P.positives.ncard
  let R := r+1
  let l := N/5
  let i := l-R
  let U := peakPrefix Y i
  let X := Y.induce Uᶜ
  let n := fixedCoreList C F.n l
  let m := fixedCoreList C F.m l
  let g : ℤ := (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)
  obtain ⟨x,y,win,heads,_,_,hist⟩ := third_gap_high_platform F paid P E hp credit gap high
  obtain ⟨sz,initial⟩ := hist i (Nat.sub_le _ _)
  change U.ncard=i at sz
  change X.edgeSet.ncard+(D-2)*i≤Y.edgeSet.ncard at initial
  have extra (b:ℕ) (cost:X.edgeSet.ncard+(D-2)*i+b≤Y.edgeSet.ncard) := third_platform_price_with_extra_edges F paid P E hp credit b cost gap high
  obtain ⟨lp,bill,fee⟩ := extra 0 (by simpa only [Nat.add_zero] using initial)
  change 0<l at lp
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at bill
  have baseline : 0≤g := by dsimp only [g];omega
  have charge (b:ℕ) (cost:X.edgeSet.ncard+(D-2)*i+b≤Y.edgeSet.ncard) :
      g+2*Z+2*l+1+b≤P.gamma h+2*(N/3+N/4:ℕ)+2*i := by
    have bound := (extra b cost).2.2
    change g+((D:ℤ)-H-1)*Z+3*l+1+b≤P.gamma h+2*(N/3+N/4:ℕ)+((D:ℤ)-H-2)*l+2*i at bound
    rw [show (D:ℤ)-H-1=2 by omega,show (D:ℤ)-H-2=1 by omega,one_mul] at bound;omega
  have first := charge 0 (by simpa only [Nat.add_zero] using initial)
  have a := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have order := a.2.2.2.2.2
  change N=2*Z+c₀ at order
  have volume : D*c₀≤2*Z := by exact_mod_cast a.2.2.2.1
  have lim := (Nat.mul_le_mul_right c₀ deg).trans volume
  have roots := P.positive_count_with_original_roots E
  have comps : c₀+1≤R+P.excess := by dsimp only [c₀,R,r];omega
  have lz : l≤Z := by dsimp only [l];omega
  obtain ⟨live,smaller,row,_⟩ := paid_fixed_exterior_cut F paid P U l lp lz (by rw [sz];exact Nat.sub_le _ _)
    (by rw [sz];change l≤r+i+1;dsimp only [i,R];omega)
  rw [sz] at live smaller row
  have shape : 3≤x ∧ 3≤y ∧ (4≤x ∨ 4≤y) := by rcases heads with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩ <;> omega
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  have row' := row
  change ForcingRow X _ _ (padDemand n) (padDemand m) (r+i+l) at row
  have actual := third_gap_fixed_head_bounds X C F.n F.m F.hn F.hm i (size ▸ lp) win high shape (by rw [size];exact row)
  rw [size] at actual
  obtain ⟨w,typed,bound,narrow,wide⟩ := actual
  change Z+1≤w+i+N/4 at narrow
  change 4≤x → 4≤y → Z+1≤w+i+l at wide
  change w≤widthAt n m (r+i+l) (D-1) at bound
  have goal := third_gap_price_alternatives D Z c₀ P.excess h R w (P.gamma h) g deg (by omega) hp
    (by dsimp only [R];omega) comps lim (by omega) (fun eleven => by have := odd eleven;omega) baseline
  dsimp only at goal;rw [←order] at goal
  apply goal (by change g+2*Z+2*l+1≤P.gamma h+2*(N/3+N/4:ℕ)+2*i;omega)
  by_cases warm:D-1≤peakFee Y i
  · left
    have save := peak_prefix_spends_at_least Y i (D-1) warm
    have cost : X.edgeSet.ncard+(D-2)*i+i≤Y.edgeSet.ncard := by
      have plus : (D-1)*i=(D-2)*i+i := by rw [←Nat.succ_mul];congr 1;omega
      rw [peak_prefix_edge_account Y i]
      change (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+_+_≤_;omega
    exact charge i cost
  · right
    have cap (v:↥(Uᶜ:Set ↥P.exterior)) : Nat.card (X.neighborSet v)≤D-2 := by
      have low := (chosenPeakStep Y U).cap v
      change Nat.card (X.neighborSet v)≤peakFee Y i at low;omega
    have hs := F.hs
    have ht := F.ht
    have seen := highest_exposure_selector_price X (q:=D-2)
      (show 0<min F.s ((componentBudget C F.n).len+l) by omega)
      (show 0<min F.t ((componentBudget C F.m).len+l) by omega) n m
      (protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l)
      (protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l)
      (protected_demand_positive F.n _ F.pn ((componentBudget C F.n).entries_positive _ F.pn) l)
      (protected_demand_positive F.m _ F.pm ((componentBudget C F.m).entries_positive _ F.pm) l) row live smaller paid (by omega) cap
    have q : D-2=H+1 := by omega
    rw [q] at seen;push_cast at seen
    change 2*((H:ℤ)+1-2)*minimumExposure X (H+1)-((H:ℤ)+1)*((H:ℤ)+1+2)≤4*g at seen
    have signedQ (arr:ExactTypedWidth X H 3 w) : (H:ℤ)*(H-1)*w-((H:ℤ)+1)*(H+3)≤4*g := by
      have exposure := true_three_head_exposure X H w (by omega) (fun v => (cap v).trans_eq q) arr
      have cost : (H:ℤ)*w≤2*minimumExposure X (H+1) := by exact_mod_cast exposure
      have add := mul_le_mul_of_nonneg_left cost (show 0≤(H:ℤ)-1 by omega)
      linarith only [seen,add]
    have eqH : (D:ℤ)-3=H := by omega
    rw [eqH]
    rcases heads with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨lx,ly⟩
    · exact Or.inl ⟨narrow,signedQ (exact_typed_width_swap X typed)⟩
    · exact Or.inl ⟨narrow,signedQ typed⟩
    · right
      refine ⟨wide lx ly,?_⟩
      have env : w≤minimumExposure X (H+1) := typed_width_exposure_at_cap X (H+1) x y w (by omega)
        (fun v => (cap v).trans_eq q) win.1 win.2.1 (by have ht := win.2.2.1;omega) typed
      have cost := mul_le_mul_of_nonneg_left (show (w:ℤ)≤minimumExposure X (H+1) by exact_mod_cast env) (show 0≤2*((H:ℤ)-1) by omega)
      linarith only [seen,cost]

#print axioms third_gap_high_is_single
end JSP452Audit.StarHost
