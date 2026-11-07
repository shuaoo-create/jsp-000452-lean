import SubcapNonunitResidualImpossible
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def OnlyUnitJoinedResidual {s D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) : Prop :=
  let μ := matchingEdges (G.induce K.core)
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W K.roots.ncard μ
  originalThresholdCount J 2=0 ∧ originalThresholdCount n 2≤μ ∧
    originalThresholdCount (W.entries n) 2≤K.roots.ncard ∧ (∀i,J i=1)

private theorem orientation_short {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (nc : n ⟨0,hs⟩<D) (mc : m ⟨0,ht⟩≤D-2)
    (escaped : matchingEdges (G.induce K.core)<s) (embedded : t≤matchingEdges (G.induce K.core))
    (alt : WholeListRegionAlternative G K.core m d)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r)) : OnlyUnitJoinedResidual G K n := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  obtain ⟨half,mass,_⟩ := alt.resolve_left (by change ¬μ+d+1≤t;change t≤μ at embedded;omega)
  have q := nontrivial_core_count_le_region_pieces G D K
  change nontrivialCoreCount (G.induce K.core)≤a+minimumExposure G D at q
  change (∑j,m j)+d≤μ+nontrivialCoreCount (G.induce K.core) at mass
  have winner := two_subcap_top_is_mixed hs ht n m hn hm pn pm live top nc mc deg
  have zero := subcap_nonunit_residual_impossible G K n m hs ht hn hm pn pm row deg cap top d rank strict width
    endpoint half (by change (∑j,m j)+d≤μ+a+minimumExposure G D;omega) reserve escaped kinds data winner
  change originalThresholdCount J 2=0 at zero
  have fit := component_budget_loss_le (G.induce K.core) n
  obtain ⟨_,f,cut,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change originalThresholdCount n 2≤μ+originalThresholdCount J 2 at f
  change originalThresholdCount (W.entries n) 2≤a+originalThresholdCount J 2 at cut
  refine ⟨zero,by change originalThresholdCount n 2≤μ;omega,by change originalThresholdCount (W.entries n) 2≤a;omega,?_⟩
  intro i
  have hi : ¬2≤J i := fun v => by
    have bad := (original_threshold_prefix J (common_erased_antitone n hn W a μ) 2 i).1 v
    omega
  have lo := common_erased_positive n W a μ i
  change 1≤J i at lo
  change J i=1;omega

/-- For both orientations, unrestricted-degree double-subcap single
escapes below the opposite boundary now force a purely unit joined
residual. Equivalently a surviving nonunit eliminates this entire case. -/
theorem strict_subcap_single_needs_unit_join (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    (μ<F.s → F.t≤μ → F.n ⟨0,F.hs⟩<D → F.m ⟨0,F.ht⟩≤D-2 → OnlyUnitJoinedResidual F.G K F.n) ∧
    (μ<F.t → F.s≤μ → F.m ⟨0,F.ht⟩<D → F.n ⟨0,F.hs⟩≤D-2 → OnlyUnitJoinedResidual F.G K F.m) := by
  intro D μ
  let d := F.rank-matchingEdges F.G
  have init : 4≤D := strict_source_degree_at_least_four F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,small,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have w := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have res := (minimal_strict_source_deficit F paid).2.1
  have alt := strict_source_whole_list_alternatives F K
  have original := original_root_endpoint_guards F paid K
  have cls := strict_single_unpaid_types F paid K
  have data := strict_common_actual_successors F paid K
  constructor
  · intro esc inner red blue
    have six := minimal_subcap_heads_force_degree_six F paid red (by change F.m ⟨0,F.ht⟩<D;omega)
    exact orientation_short F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row F.live six cap top d rank F.strict w res
      red blue esc inner alt.2 original.1 (cls.1 esc inner) (data.1 esc)
  · intro esc inner blue red
    have six := minimal_subcap_heads_force_degree_six F paid (by change F.n ⟨0,F.hs⟩<D;omega) blue
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have eq := row_energy_colour_swap F.m F.n F.r
    exact orientation_short F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn (swap_positive_forcing_row F.G _ _ F.row)
      (by rw [swap];exact F.live) six cap ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm)
      (by rw [eq];exact F.strict) ((highest_width_colour_swap _ _ _).le.trans w) res
      blue red esc inner alt.1 original.2 (cls.2 esc inner) (by rw [swap,eq];exact data.2 esc)

#print axioms strict_subcap_single_needs_unit_join
end JSP452Audit.StarHost
