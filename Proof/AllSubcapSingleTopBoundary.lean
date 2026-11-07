import SingleEscapeLargeTopExcluded
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def TwoHeadTopBoundary {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t) (r D : ℕ) : Prop :=
  m ⟨0,ht⟩=D-1 ∧ WinsHeight n m r D 2 (D-1) ∧
    ∀x y,WinsHeight n m r D x y → x=2 ∧ y=D-1

private theorem force_top_boundary {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (nc : n ⟨0,hs⟩<D) (mc : m ⟨0,ht⟩<D)
    (esc : matchingEdges (G.induce K.core)<s) (inner : t≤matchingEdges (G.induce K.core))
    (alt : WholeListRegionAlternative G K.core m d)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+
      (matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)≤s-matchingEdges (G.induce K.core))
    (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r)) : TwoHeadTopBoundary n m ht r D := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  obtain ⟨half,mass,_⟩ := alt.resolve_left (by change ¬μ+d+1≤t;change t≤μ at inner;omega)
  have q := nontrivial_core_count_le_region_pieces G D K
  change nontrivialCoreCount (G.induce K.core)≤a+minimumExposure G D at q
  change (∑j,m j)+d≤μ+nontrivialCoreCount (G.induce K.core) at mass
  obtain ⟨i,j,_,eq⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have ncap := hn (show (⟨0,hs⟩:Fin s) ≤ i from Nat.zero_le _)
  have g3 := (original_threshold_prefix m hm 3 j).1 (by omega)
  have excl := single_escape_large_top_impossible G K n m hs ht hn hm pn pm row live deg cap top d rank strict width
    reserve endpoint guard half (by change (∑j,m j)+d≤μ+a+minimumExposure G D;omega) esc kinds data mc.le (by omega)
  have classify (x y:ℕ) (win:WinsHeight n m r D x y) : x=2 ∧ y=D-1 := by
    have both := win.2.2.1
    have n0 := (original_threshold_prefix n hn x ⟨0,hs⟩).2 win.2.2.2.1
    have m0 := (original_threshold_prefix m hm y ⟨0,ht⟩).2 win.2.2.2.2.1
    by_cases hi : 3≤x
    · exact (excl ⟨x,y,hi,by omega,win⟩).elim
    · omega
  have pos := actual_height_positive n m live top D (by omega)
  obtain ⟨x,y,px,py,h,pn',pm',rect⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<D) pos
  have win : WinsHeight n m r D x y := ⟨px,py,h,pn',pm',rect⟩
  obtain ⟨xe,ye⟩ := classify _ _ win
  have bound := (original_threshold_prefix m hm y ⟨0,ht⟩).2 pm'
  rw [xe,ye] at win
  exact ⟨by omega,win,classify⟩

/-- In a double-subcap single escape, the opposite head must equal
D-1 and every winner at height D must be exactly (2,D-1). -/
theorem strict_subcap_single_forces_top_boundary (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    F.n ⟨0,F.hs⟩<D → F.m ⟨0,F.ht⟩<D →
      (μ<F.s → F.t≤μ → TwoHeadTopBoundary F.n F.m F.ht F.r D) ∧
      (μ<F.t → F.s≤μ → TwoHeadTopBoundary F.m F.n F.hs F.r D) := by
  intro D μ nc mc
  let d := F.rank-matchingEdges F.G
  have six : 6≤D := minimal_subcap_heads_force_degree_six F paid nc mc
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,small,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have w := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have reserve := (minimal_strict_source_deficit F paid).2.1
  have alt := strict_source_whole_list_alternatives F K
  have own := original_root_endpoint_guards F paid K
  have guard := strict_exterior_endpoint_guards F paid K
  have cls := strict_single_unpaid_types F paid K
  have data := strict_common_actual_successors F paid K
  constructor
  · intro esc inner
    exact force_top_boundary F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row F.live six cap top d rank F.strict w
      reserve nc mc esc inner alt.2 own.1 (guard.1 esc) (cls.1 esc inner) (data.1 esc)
  · intro esc inner
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have eq := row_energy_colour_swap F.m F.n F.r
    exact force_top_boundary F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn (swap_positive_forcing_row F.G _ _ F.row)
      (by rw [swap];exact F.live) six cap ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm)
      (by rw [eq];exact F.strict) ((highest_width_colour_swap _ _ _).le.trans w) reserve mc nc esc inner alt.1 own.2
      (guard.2 esc) (cls.2 esc inner) (by rw [swap,eq];exact data.2 esc)

#print axioms strict_subcap_single_forces_top_boundary
end JSP452Audit.StarHost
