import TheFinalThreeActualNineColumns
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Interchange both original demand lists on the identical host. -/
def StrictFamily.exchangeSides (F : StrictFamily.{u}) : StrictFamily.{u} where
  X := F.X
  G := F.G
  s := F.t
  t := F.s
  r := F.r
  n := F.m
  m := F.n
  hs := F.ht
  ht := F.hs
  hn := F.hm
  hm := F.hn
  pn := F.pm
  pm := F.pn
  live := by simpa only [rowCount,Nat.add_comm F.t F.s] using F.live
  row := swap_positive_forcing_row F.G _ _ F.row
  strict := by rw [row_energy_colour_swap F.m F.n];exact F.strict

theorem strict_source_degree_nine_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) : False := by
  obtain ⟨R,aligned,branches⟩ := strict_nine_aligned_short_source_exists F paid nine
  rcases branches with short|short
  · let B := F.exchangeSides
    have rank : B.rank=F.rank := by change rowCount F.t F.s F.r=rowCount F.s F.t F.r;simp [rowCount,Nat.add_comm]
    have nine' : diagonal B.n B.m (B.r+2)-1=9 := by
      change diagonal F.m F.n (F.r+2)-1=9
      rw [diagonal_swap F.m F.n];exact nine
    have aligned' : (highestWidth B.n B.m B.r:ℤ)≤R.K.eta := by
      change (highestWidth F.m F.n F.r:ℤ)≤R.K.eta
      rw [highest_width_colour_swap F.m F.n];exact aligned
    exact strict_nine_last_boundary_impossible B (rank.symm ▸ paid) nine' R aligned'
      (by change R.totalCapacity<F.t;omega) (by change F.s≤R.totalCapacity;omega)
  · exact strict_nine_last_boundary_impossible F paid nine R aligned (by omega) (by omega)

theorem strict_source_degree_at_least_ten (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    10≤diagonal F.n F.m (F.r+2)-1 := by
  have lower := strict_source_degree_at_least_nine F paid
  by_contra! small
  exact strict_source_degree_nine_impossible F paid (by omega)

theorem original_failure_needs_degree_ten {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 10≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,_,edges,order,esc⟩ := original_failure_needs_degree_nine hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_ten F paid,edges,order,esc⟩

#print axioms strict_source_degree_nine_impossible
#print axioms strict_source_degree_at_least_ten
#print axioms original_failure_needs_degree_ten
end JSP452Audit.StarHost
