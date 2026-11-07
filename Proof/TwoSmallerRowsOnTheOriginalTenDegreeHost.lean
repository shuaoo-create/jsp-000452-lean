import AtLeastEtaLargeActualTenDegreeCoreComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem TenBlockPartition.ten_budget_loss {s:ℕ} {X:Type u} [Finite X] {G:SimpleGraph X} (R:TenBlockPartition G)
    (hs:0<s) (n:Fin s→ℕ) (heads:∀i,n i≤9) (cap:∀x,Nat.card (G.neighborSet x)≤10)
    (small:R.epsilon≤2) (many:1≤R.eta) :
    1≤(componentBudget R.coreGraph n).loss ∧ (componentBudget R.coreGraph n).loss≤R.capacity := by
  obtain ⟨large,volume⟩ := R.many_large_components cap small
  obtain ⟨c,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<R.largeComponents.ncard by omega)
  let i : Fin s := ⟨0,hs⟩
  change 11≤Nat.card c.supp at mem
  have rank : 0<matchingEdges R.coreGraph := by change 0<R.capacity;omega
  have one := component_budget_accepts_singleton R.coreGraph n i c rank (by have := heads i;omega)
  exact ⟨one,component_budget_loss_le _ _⟩

theorem ten_same_budget_on_two_graphs (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : TenBlockPartition F.G) :
    let C := F.G.induce R.core
    let O := F.G.induce R.rest
    let Z := eraseInternal F.G R.core
    let P := R.capacity
    let a := R.roots.ncard
    let W := componentBudget C F.n
    let V := componentBudget C F.m
    (ForcingRow O W.len F.t (padDemand (W.entries F.n)) (padDemand F.m) (F.r+a) ∧
      ForcingRow Z W.len F.t (padDemand (commonErasedDemand F.n W a P)) (padDemand F.m) F.r) ∧
    (ForcingRow O V.len F.s (padDemand (V.entries F.m)) (padDemand F.n) (F.r+a) ∧
      ForcingRow Z V.len F.s (padDemand (commonErasedDemand F.m V a P)) (padDemand F.n) F.r) := by
  intro C O Z P a W V
  have row := (ten_physical_root_deleted_row F paid R).2.2.2
  have wn := component_budget_admits C F.n F.pn
  have vm := component_budget_admits C F.m F.pm
  have one := R.complete_erased_core_row F.G W F.n F.m F.hn F.pn wn F.row
  have two := R.complete_erased_core_row F.G V F.m F.n F.hm F.pm vm (swap_positive_forcing_row _ _ _ F.row)
  exact ⟨⟨one_budget_on_sum_row O C F.n F.m F.pm W wn row,one⟩,
    ⟨one_budget_on_sum_row O C F.m F.n F.pn V vm (swap_positive_forcing_row _ _ _ row),two⟩⟩


theorem ten_long_side_two_prices (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s) :
    let P := R.capacity
    let a := R.roots.ncard
    let O := F.G.induce R.rest
    let Z := eraseInternal F.G R.core
    let W := componentBudget (F.G.induce R.core) F.n
    let J := commonErasedDemand F.n W a P
    let d' := F.rank-matchingEdges F.G
    let delta := P-W.loss
    0<W.len ∧ 1≤W.loss ∧ W.loss≤P ∧
      rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta ∧
      rowCount W.len F.t F.r=a+R.outsideRank+d'+delta ∧
      0<rowCount W.len F.t (F.r+a) ∧ rowCount W.len F.t F.r<F.rank ∧
      rowEnergy (W.entries F.n) F.m (F.r+a)≤O.edgeSet.ncard ∧
      rowEnergy J F.m F.r≤Z.edgeSet.ncard ∧
      rowEnergy (W.entries F.n) F.m (F.r+a)+rowEnergy J F.m F.r+10*(a+2*P)+10*R.eta+
        (F.G.induce R.roots).edgeSet.ncard+crossCount F.G R.roots R.rest≤2*F.G.edgeSet.ncard+R.epsilon := by
  intro P a O Z W J d' delta
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  obtain ⟨red,_,_⟩ := strict_only_double_escape F paid
  have head (i) : F.n i≤9 := by have lim := red i;rw [ten] at lim;omega
  obtain ⟨positive,fit⟩ := R.ten_budget_loss F.hs F.n head cap small many
  change 1≤W.loss at positive
  change W.loss≤P at fit
  have alive : 0<W.len := by change 0<F.s-W.loss;omega
  have number : W.len+W.loss=F.s := by change F.s-W.loss+W.loss=F.s;omega
  obtain ⟨dp,balance,_,_⟩ := ten_physical_root_deleted_row F paid R
  change 2≤d' at dp
  change F.s+F.t-1-(F.r+a)=P+R.outsideRank+d' at balance
  have ranks : rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta ∧
      rowCount W.len F.t F.r=a+R.outsideRank+d'+delta := by
    dsimp only [rowCount,delta];omega
  have smaller : rowCount W.len F.t F.r<F.rank := by dsimp [StrictFamily.rank,rowCount];omega
  have s2 : rowCount W.len F.t (F.r+a)<F.rank := by dsimp only [rowCount] at smaller ⊢;omega
  have rows := (ten_same_budget_on_two_graphs F paid R).1
  have payO := paid alive F.ht (W.entries F.n) F.m (W.entries_antitone F.n F.hn) F.hm
    (W.entries_positive F.n F.pn) F.pm O (F.r+a) rows.1 s2
  have payZ := paid alive F.ht J F.m (common_erased_antitone F.n F.hn W a P) F.hm
    (common_erased_positive F.n W a P) F.pm Z F.r rows.2 smaller
  have fee := (R.edge_fees cap).2.2.2.1
  change 2*F.G.edgeSet.ncard+R.epsilon=O.edgeSet.ncard+Z.edgeSet.ncard+10*(a+2*P)+10*R.eta+_+_ at fee
  exact ⟨alive,positive,fit,ranks.1,ranks.2,by omega,smaller,payO,payZ,by omega⟩

#print axioms TenBlockPartition.ten_budget_loss
#print axioms ten_same_budget_on_two_graphs
#print axioms ten_long_side_two_prices
end JSP452Audit.StarHost
