import OriginalPeakParityAndFactorCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_double_head_gap_range (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let A := F.n ⟨0,F.hs⟩
    let B := F.m ⟨0,F.ht⟩
    let γ := D-max A B
    1≤γ ∧ D+2≤A+B ∧ γ+2≤min A B ∧ 2*γ+2≤D := by
  intro D A B γ
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  obtain ⟨i,j,_,_,_,sum,_⟩ := strict_actual_peak_factor_obstruction F paid
  have n := F.hn (show (⟨0,F.hs⟩:Fin F.s)≤ i from Nat.zero_le _)
  have m := F.hm (show (⟨0,F.ht⟩:Fin F.t)≤j from Nat.zero_le _)
  have topN : A<D := red ⟨0,F.hs⟩
  have topM : B<D := blue ⟨0,F.ht⟩
  change F.n i+F.m j=D+2 at sum;change F.n i≤A at n;change F.m j≤B at m
  dsimp only [γ];omega

theorem strict_six_balanced_factor_cut (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (six : diagonal F.n F.m (F.r+2)-1=6) :
    let h := highestWidth F.n F.m F.r
    ∃(i:Fin F.s) (j:Fin F.t) (u v:ℕ),i.val+j.val=F.r ∧ F.n i=4 ∧ F.m j=4 ∧
      0<u ∧ 0<v ∧ u≤headWidth F.n i ∧ v≤headWidth F.m j ∧ u+v-1=h ∧
      Forces F.G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 4)) ∧
      ∃S T:Set F.X,Disjoint S T ∧ (h:ℤ)≤originalFactorCut F.G 3 3 S T := by
  intro h
  obtain ⟨i,j,u,v,idx,sum,r0,r1,b0,b1,pu,pv,ur,vr,wide,force,parity,S,T,apart,cut⟩ := strict_actual_peak_factor_obstruction F paid
  rw [six] at r1 b1 sum parity
  obtain ⟨nr,mb⟩ := parity (by decide)
  have red : F.n i=4 := by omega
  have blue : F.m j=4 := by omega
  rw [red,blue] at force cut
  exact ⟨i,j,u,v,idx,red,blue,pu,pv,ur,vr,wide,force,S,T,apart,cut⟩

theorem original_failure_double_escape_with_cut {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      OnlyDoubleEscape F ∧ ActualPeakObstruction F := by
  obtain ⟨F,paid,deg,edges,order,types⟩ := original_failure_only_double_escape.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,types,strict_actual_peak_factor_obstruction F paid⟩

#print axioms strict_double_head_gap_range
#print axioms strict_six_balanced_factor_cut
#print axioms original_failure_double_escape_with_cut
end JSP452Audit.StarHost