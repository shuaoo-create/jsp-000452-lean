import AllRemainingHeadGapsOnOneActualMinimumSource
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def OriginalUniformPeak {X:Type u} [Finite X] (G:SimpleGraph X) (h p q:ℕ) : Prop :=
  ∃u v,0<u ∧ 0<v ∧ u+v-1=h ∧ Forces G (forest (fun _:Fin u => p+1)) (forest (fun _:Fin v => q+1)) ∧
    ∃S T:Set X,Disjoint S T ∧ (h:ℤ)≤originalFactorCut G p q S T

theorem strict_oriented_high_peak (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    ∃p q,2≤p ∧ 2≤q ∧ p+q=D ∧ OriginalUniformPeak F.G h p q ∧
      (D%2=1 → p%2=1 ∧ q%2=0) ∧ (D%2=0 → p%2=1 ∧ q%2=1 ∧ p≤q) ∧
      (∃i j,i.val+j.val=F.r ∧ ((F.n i=p+1 ∧ F.m j=q+1) ∨ (F.n i=q+1 ∧ F.m j=p+1))) := by
  intro D h
  obtain ⟨i,j,u,v,idx,sum,lo,hi,lo',hi',up,vp,_,_,wide,force,parity,S,T,dis,cut⟩ :=
    strict_actual_peak_factor_obstruction F paid
  let p := F.n i-1
  let q := F.m j-1
  have np : F.n i=p+1 := by dsimp only [p];omega
  have mq : F.m j=q+1 := by dsimp only [q];omega
  change F.n i+F.m j=D+2 at sum
  change u+v-1=h at wide
  have cap (z) : Nat.card (F.G.neighborSet z)≤D := (minimal_rank_exact_source F paid).2.2.2.1 z
  have even : D%2=0 → p%2=1 ∧ q%2=1 := by intro ok;obtain ⟨a,b⟩ := parity ok;omega
  have keep : OriginalUniformPeak F.G h p q := by
    exact ⟨u,v,up,vp,wide,by rwa [←np,←mq],S,T,dis,cut⟩
  have reverse : OriginalUniformPeak F.G h q p := by
    obtain ⟨A,B,apart,price⟩ := original_uniform_factor_cut F.G (F.m j) (F.n i) v u (by omega) (by omega) vp up
      (fun z => (cap z).trans (by omega)) (forces_swap force)
    exact ⟨v,u,vp,up,by omega,by rw [←np,←mq];exact forces_swap force,A,B,apart,by simpa only [Nat.add_comm v u,wide] using price⟩
  by_cases odd:D%2=1
  · by_cases first:p%2=1
    · exact ⟨p,q,by omega,by omega,by omega,keep,by omega,by omega,i,j,idx,Or.inl ⟨np,mq⟩⟩
    · exact ⟨q,p,by omega,by omega,by omega,reverse,by omega,by omega,i,j,idx,Or.inr ⟨np,mq⟩⟩
  · obtain ⟨ep,eq⟩ := even (by omega)
    by_cases less:p≤q
    · exact ⟨p,q,by omega,by omega,by omega,keep,by omega,by omega,i,j,idx,Or.inl ⟨np,mq⟩⟩
    · exact ⟨q,p,by omega,by omega,by omega,reverse,by omega,by omega,i,j,idx,Or.inr ⟨np,mq⟩⟩

#print axioms strict_oriented_high_peak
end JSP452Audit.StarHost
