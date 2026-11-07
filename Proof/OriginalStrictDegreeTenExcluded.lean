import TheTwoPossibleNinthColumnCostsOnTheActualPortHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 1000000 in
theorem strict_source_degree_ten_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) : False := by
  obtain ⟨width,_,deep,eight,K,W,_,_,_,_,length,_⟩ := strict_ten_same_partition_and_port_support F paid ten
  let O := W.outside
  let h := highestWidth F.n F.m F.r
  let P := W.half
  let M := W.slotDamage
  let L := widthAt F.n F.m F.r
  have narrow : h≤2 := by change h=1 ∨ h=2 at width;omega
  obtain ⟨H⟩ := three_degree_stages_exist O 8
  obtain ⟨red,blue,_,_,fee⟩ := ten_port_actual_last_two_cost F paid ten W narrow deep length eight H
  change 2*W.rank+W.fee+1+H.upper.ncard+H.midCut.ncard≤L 9+L 10+h at fee
  have cap (v:↥(W.supportᶜ:Set F.X)) := (induced_neighbor_count_le F.G W.supportᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq ten)
  have first := (H.degree_caps cap).1
  have second := (H.degree_caps cap).2.1
  obtain ⟨exp₉,exp₈⟩ := ten_port_second_stage_exposure F paid ten W narrow length red blue H
  have upper := ten_signed_port_tenth_column F paid ten W H.upper first 3 (by decide)
    (fun i => by have := red i;omega) (fun j => by have := blue j;omega)
  change L 10-H.upper.ncard≤M 3+max (h-1) (minimumExposure (O.induce H.upperᶜ) 9-2) at upper
  have ninth := ten_ninth_column_on_second_port_cut F W red blue H.midCut second
  change L 9≤P+4 ∨ L 9-H.midCut.ncard≤M 2+minimumExposure (O.induce H.midCutᶜ) 8 at ninth
  change minimumExposure (O.induce H.upperᶜ) 9≤6 at exp₉
  change minimumExposure (O.induce H.midCutᶜ) 8≤7 at exp₈
  have pos := (strict_ten_inventory F paid ten).1
  have prices := W.port_slot_sizes pos
  change 3*M 2≤2*P+W.parity+2*W.portCount ∧ 4*M 3≤2*P+W.parity+3*W.portCount ∧ _ at prices
  have book := W.size_and_fee pos
  have min : 22≤P := book.2.2.2.2.2.1
  have fit : W.rank≤P := book.2.2.2.2.1
  have eps := book.2.2.1
  have ports := book.2.1
  have bill : W.fee+1=10*(P-W.rank)+5*W.parity+W.portCount := book.2.2.2.2.2.2.2.2.2.2
  clear * - fee upper ninth exp₉ exp₈ prices min fit eps ports bill narrow
  omega

theorem strict_source_degree_at_least_eleven (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    11≤diagonal F.n F.m (F.r+2)-1 := by
  have bound := strict_source_degree_at_least_ten F paid
  by_contra! small;exact strict_source_degree_ten_impossible F paid (by omega)

theorem original_failure_needs_degree_eleven {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 11≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,_,edges,order,esc⟩ := original_failure_needs_degree_ten hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_eleven F paid,edges,order,esc⟩

#print axioms strict_source_degree_ten_impossible
#print axioms strict_source_degree_at_least_eleven
#print axioms original_failure_needs_degree_eleven
end JSP452Audit.StarHost
