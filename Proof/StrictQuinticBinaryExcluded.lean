import QuinticBinaryActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quintic_binary_zero_row_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (zero:r=0) (five:D=5) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (binary : m ⟨0,ht⟩=2) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d) (root : 3*minimumExposure G D+rootShortfall G K.roots D≤10)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  subst r
  exact quintic_binary_nonunit_paid G K n m hs ht hn hm pn pm five cap live row head binary top d rank data esc inner
    (by simpa using endpoint) width reserve root trigger nonunit

theorem strict_zero_quintic_binary_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (zero : F.r=0) (five : diagonal F.n F.m (F.r+2)-1=5)
    (binary : (F.n ⟨0,F.hs⟩=5 ∧ F.m ⟨0,F.ht⟩=2) ∨ (F.m ⟨0,F.ht⟩=5 ∧ F.n ⟨0,F.hs⟩=2)) : False := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  let μ := matchingEdges (F.G.induce K.core)
  let a := K.roots.ncard
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have root := ((low_degree_original_costs F paid K).2.2 five).2.1
  have cost : 3*minimumExposure F.G D+rootShortfall F.G K.roots D≤10 := by
    change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤10 at root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have mass := strict_source_whole_list_alternatives F K
  have data := strict_both_complete_exteriors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have nonunit := strict_full_binary_nonunit_remaining F paid K
  have bad := F.strict
  rcases binary with ⟨red,blue⟩|⟨blue,red⟩
  · have full : F.n ⟨0,F.hs⟩=D := red.trans five.symm
    obtain ⟨embedded,len,_,_⟩ := unique.1 full
    change μ+a+F.r+d+1≤F.s at len
    have escaped : μ<F.s := by omega
    change F.t≤μ at embedded
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    have fee := quintic_binary_zero_row_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm zero five cap F.live F.row
      full blue top d rank (data.1 escaped) escaped (by change F.t+d≤μ+1;omega) guards.1 width res cost
      (trigger.1 full) (nonunit.1 full blue)
    omega
  · have full : F.m ⟨0,F.ht⟩=D := blue.trans five.symm
    obtain ⟨embedded,len,_,_⟩ := unique.2 full
    change μ+a+F.r+d+1≤F.t at len
    have escaped : μ<F.t := by omega
    change F.s≤μ at embedded
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have H := highest_width_colour_swap F.m F.n F.r
    have fee := quintic_binary_zero_row_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn zero five cap (by rw [swap];exact F.live)
      (swap_positive_forcing_row F.G _ _ F.row) full red ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm)
      (by rw [swap];exact data.2 escaped) escaped (by change F.s+d≤μ+1;omega) guards.2 (by rw [H];exact width)
      res cost (trigger.2 full) (nonunit.2 full red)
    rw [row_energy_colour_swap F.m F.n] at fee;omega

theorem strict_quintic_binary_excluded (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) :
    ¬ ((F.n ⟨0,F.hs⟩=5 ∧ F.m ⟨0,F.ht⟩=2) ∨ (F.m ⟨0,F.ht⟩=5 ∧ F.n ⟨0,F.hs⟩=2)) := by
  intro bin
  obtain ⟨T,same,other,_⟩ := strict_full_binary_zero_entry F paid (by dsimp only;rw [five];exact bin)
  obtain ⟨zero,_,_,_,_,nh,mh,cols,_,_⟩ := same
  have eq := cols 0
  simp only [Nat.add_zero,Nat.zero_add] at eq
  exact strict_zero_quintic_binary_impossible T other zero (by rw [zero];simpa [eq] using five)
    (by rw [nh,mh];exact bin)

#print axioms quintic_binary_zero_row_paid
#print axioms strict_zero_quintic_binary_impossible
#print axioms strict_quintic_binary_excluded
end JSP452Audit.StarHost