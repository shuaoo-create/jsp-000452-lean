import SixDegreeExposurePriceOnAnyRow
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_source_degree_seven_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) : False := by
  classical
  obtain ⟨K⟩ := degreeRegion_exists F.G 7
  let _ := Fintype.ofFinite ↥K.positive
  have four := (strict_seven_four_positive_pieces F paid seven K).1
  have some : K.positive.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨q,hq⟩ := some
  have non : (Finset.univ:Finset ↥K.positive).Nonempty := ⟨⟨q,hq⟩,Finset.mem_univ _⟩
  obtain ⟨p,_,min⟩ := Finset.exists_min_image Finset.univ K.pieceCapacity non
  have smallest (q:↥K.positive) := min q (Finset.mem_univ q)
  obtain ⟨S⟩ := SevenPiece.actual_descent F K p paid seven smallest
  let Y := (SevenPiece.erased F K p).induce S.removedᶜ
  obtain ⟨five,size,upper⟩ := SevenPiece.restored_successor_exposure F paid seven K p smallest S
  have rho : 5≤minimumExposure Y 6 := five.trans size
  have lower := six_exposure_price_on_actual_row F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y
    (SevenPiece.nextRow F K p) F.rank S.row S.live S.smaller.le paid S.cap S.height rho
  exact (not_lt_of_ge lower) upper

theorem strict_source_degree_at_least_eight (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    8≤diagonal F.n F.m (F.r+2)-1 := by
  have lower := strict_source_degree_at_least_seven F paid
  by_contra! small
  exact strict_source_degree_seven_impossible F paid (by omega)

theorem original_failure_needs_degree_eight {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 8≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,_,edges,order,regime⟩ := original_failure_needs_degree_seven.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_eight F paid,edges,order,regime⟩

#print axioms strict_source_degree_seven_impossible
#print axioms strict_source_degree_at_least_eight
#print axioms original_failure_needs_degree_eight
end JSP452Audit.StarHost
