import FinalEighthColumnOnSelectedComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_source_degree_eight_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) : False := by
  classical
  obtain ⟨j,positive,types,e,actual⟩ := actual_eight_selection F paid eight
  let _ : Nonempty (Fin j) := ⟨⟨0,positive⟩⟩
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := ∑c∈T,Nat.card c.supp/2
  let h := highestWidth F.n F.m F.r
  let L7 := widthAt F.n F.m F.r 7
  let L8 := widthAt F.n F.m F.r 8
  have members (c) (mem:c∈T) : c∈oddRegularComponents F.G 8 := by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem;exact actual i
  have count : T.card=j := by simp [T]
  have kind : EightSelectionSize T.card h := count.symm ▸ types
  have kindI : EightSelectionSize (Fintype.card (Fin j)) h := by rwa [Fintype.card_fin]
  have total : (∑i,Nat.card (e i).supp/2)=P := by dsimp only [P,T];rw [Finset.sum_map]
  have per (c) (mem:c∈T) : 4≤Nat.card c.supp/2 := by
    let v := c.nonempty_supp.to_subtype.some
    exact half_order_of_regular_component c.toSimpleGraph 4 v ((component_degree_eq F.G c v).trans ((members c mem).2 v.val v.property))
  have ord := Finset.sum_le_sum (s:=T) per
  rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at ord
  obtain ⟨H⟩ := eight_seven_six_history_exists O
  let b := H.eight.ncard
  let c := H.sevenCut.ncard
  let rho := minimumExposure (O.induce H.sevenCutᶜ) 6
  have price := (exact_eight_penultimate_price F paid eight e actual kindI H).2.2
  rw [total,Fintype.card_fin] at price
  change 2*P+4*j+1+b+c≤L7+L8+h at price
  have fee : 2*P+4*T.card+1+b+c≤L7+L8+h := by omega
  have shadow := (strict_signed_first_stage_on_exterior F paid eight T members H).1
  have col6 := strict_eight_second_exterior_exposure F paid eight U (component_vertices_closed F.G T) H
  have seventh := seven_column_survives_or_within_half_order F paid eight T H
  have localBounds := eighth_column_small_remaining_bounds F paid eight T members kind H
  have resource := regular_half_order_slot_counts F.G 8 T members
  have fourth := chosen_width_four_slot_bound F.G T members
  exact eight_penultimate_prices_incompatible P T.card h L7 L8 b c (chosenSlots F.G T 2) (chosenSlots F.G T 3)
    (chosenSlots F.G T 4) rho kind (by change T.card*4≤P at ord;omega)
    resource.1 resource.2 fourth fee shadow seventh col6 localBounds.1 localBounds.2

theorem strict_source_degree_at_least_nine (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    9≤diagonal F.n F.m (F.r+2)-1 := by
  have lo := strict_source_degree_at_least_eight F paid
  by_contra! small
  exact strict_source_degree_eight_impossible F paid (by omega)

theorem original_failure_needs_degree_nine {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 9≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,_,edges,order,regime⟩ := original_failure_needs_degree_eight.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_nine F paid,edges,order,regime⟩

#print axioms strict_source_degree_eight_impossible
#print axioms strict_source_degree_at_least_nine
#print axioms original_failure_needs_degree_nine
end JSP452Audit.StarHost
