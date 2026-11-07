import BothNineSingleShortRowsHavePositiveSmallerRank
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

theorem tight_cut_size_after_exact_rank_loss {X : Type*} [Finite X] (G : SimpleGraph X)
    (A : Set X) (rank : matchingEdges G=A.ncard+matchingEdges (G.induce Aᶜ)) :
    ∃S : Set X,IsTightBarrier G S ∧ A.ncard≤S.ncard ∧
      ∀c : (G.induce Sᶜ).ConnectedComponent,Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph := by
  obtain ⟨B,tightB⟩ := tutte_berge_attained (G.induce Aᶜ)
  have nG := minUnmatched_add_twice_matching G
  have nA := minUnmatched_add_twice_matching (G.induce Aᶜ)
  rw [Nat.card_coe_set_eq] at nA
  have count := Set.ncard_add_ncard_compl A
  have unmatched : minUnmatched (G.induce Aᶜ)=minUnmatched G+A.ncard := by omega
  have joined : IsTightBarrier G (outerCut A B) := by
    change (G.induce (outerCut A B)ᶜ).oddComponents.ncard=(outerCut A B).ncard+minUnmatched G
    rw [←odd_ncard_iso (nestedCutIso G A B),tightB,outerCut_ncard,unmatched];omega
  obtain ⟨S,tight,large⟩ := exists_largest_tight_barrier G
  have size := large (outerCut A B) joined
  rw [outerCut_ncard] at size
  exact ⟨S,tight,by omega,largest_barrier_components G S tight large⟩

theorem strict_nine_original_root_endpoints (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) :
    let a := R.roots.ncard
    let d' := F.rank-matchingEdges F.G-R.rankAllowance
    a+F.r+2*(d'+∑i,(F.n i-1)/2)≤F.t ∧
      a+F.r+2*(d'+∑j,(F.m j-1)/2)≤F.s := by
  intro a d'
  let d := F.rank-matchingEdges F.G
  have below := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp only [d];omega
  have eq : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp only [d];omega
  have count : a≤2 := R.root_count.2
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have allowance := R.root_deleted_rank_allowance cap
  by_cases loss : R.rankAllowance=0
  · have actual := (R.region_rank_edges cap).2.2.1
    have rank : matchingEdges F.G=R.roots.ncard+matchingEdges (F.G.induce R.rootsᶜ) := by omega
    obtain ⟨S,tight,big,critical⟩ := tight_cut_size_after_exact_rank_loss F.G R.roots rank
    have prices := full_row_endpoint_guards F.G F.hs F.ht F.n F.m F.pn F.pm F.row S tight
      (fun c => (critical c).2) d pos eq
    have same : d'=d := by dsimp [d',d];rw [loss,Nat.sub_zero]
    rw [same];change a≤S.ncard at big
    omega
  · obtain ⟨S,tight,critical⟩ := exists_critical_barrier F.G
    have prices := full_row_endpoint_guards F.G F.hs F.ht F.n F.m F.pn F.pm F.row S tight
      (fun c => (critical c).2) d pos eq
    have small : 2≤d' := (strict_nine_root_deleted_row F paid nine R).1
    have extra : d'+1≤d := by dsimp only [d',d] at *;omega
    omega

theorem nine_long_side_exterior_endpoints (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s) :
    let P := R.totalCapacity
    let a := R.roots.ncard
    let W := componentBudget (F.G.induce R.chosen) F.n
    let delta := P-W.loss
    let d' := F.rank-matchingEdges F.G-R.rankAllowance
    a+F.r+2*(d'+∑j,(F.m j-1)/2)+delta≤F.s-P ∧
      a+F.r+2*(d'+delta+∑i,(W.entries F.n i-1)/2)≤F.t := by
  intro P a W delta d'
  have paidRow := nine_long_side_actual_source_prices F paid nine R long
  obtain ⟨alive,_,fit,rank,_,_,_,_⟩ := paidRow
  change 0<W.len at alive
  change W.loss≤P at fit
  change rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta at rank
  let O := F.G.induce R.outside
  obtain ⟨S,tight,critical⟩ := exists_critical_barrier O
  have pos : 2≤d' := (strict_nine_root_deleted_row F paid nine R).1
  have row := (strict_nine_two_physical_rows F paid nine R).1.1
  change ForcingRow O W.len F.t (padDemand (W.entries F.n)) (padDemand F.m) (F.r+a) at row
  have prices := full_row_endpoint_guards O alive F.ht (W.entries F.n) F.m
    (W.entries_positive F.n F.pn) F.pm row S tight (fun c => (critical c).2) (d'+delta) (by omega) (by
      change R.outsideRank+(d'+delta)=rowCount W.len F.t (F.r+a);omega)
  change S.ncard+(F.r+a)+2*(d'+delta+∑i,(W.entries F.n i-1)/2)≤F.t ∧
    S.ncard+(F.r+a)+2*(d'+delta+∑j,(F.m j-1)/2)≤W.len at prices
  have len : W.len=F.s-W.loss := rfl
  dsimp only [delta] at prices ⊢
  omega

#print axioms tight_cut_size_after_exact_rank_loss
#print axioms strict_nine_original_root_endpoints
#print axioms nine_long_side_exterior_endpoints
end JSP452Audit.StarHost
