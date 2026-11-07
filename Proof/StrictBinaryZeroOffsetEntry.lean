import MaximumTailStrictSource
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The new lists are explicit tails, with equal row energies at every
later offset. The strict host itself is retained by an identity graph
isomorphism in the construction. -/
def SamePeakZeroRow (F T : StrictFamily.{u}) : Prop :=
  T.r=0 ∧ Nonempty (T.G ≃g F.G) ∧ T.rank=F.rank ∧ T.edges=F.edges ∧ T.order=F.order ∧
    T.n ⟨0,T.hs⟩=F.n ⟨0,F.hs⟩ ∧ T.m ⟨0,T.ht⟩=F.m ⟨0,F.ht⟩ ∧
    (∀k,diagonal T.n T.m (k+2)=diagonal F.n F.m (F.r+k+2)) ∧
    (∀z,rowEnergy T.n T.m z=rowEnergy F.n F.m (F.r+z)) ∧
    highestWidth T.n T.m 0=highestWidth F.n F.m F.r

theorem strict_maximum_plateau_zero_entry (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (peak : diagonal F.n F.m (F.r+2)=F.n ⟨0,F.hs⟩+F.m ⟨0,F.ht⟩-1) :
    ∃T:StrictFamily.{u},SamePeakZeroRow F T ∧ AllSmallerPaid.{u} T.rank := by
  obtain ⟨i,j,cut,ni,mj⟩ := retained_maximum_corner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.live peak
  have red (z : Fin F.s) : F.n z≤F.n i := ni ▸ F.hn (show (⟨0,F.hs⟩ : Fin F.s)≤z from Nat.zero_le _)
  have blue (z : Fin F.t) : F.m z≤F.m j := mj ▸ F.hm (show (⟨0,F.ht⟩ : Fin F.t)≤z from Nat.zero_le _)
  let T := maximumTailSource F i j cut red blue
  obtain ⟨zero,rk,ed,ord,ap,head,other,energy,width⟩ := maximum_tail_source_minima F i j cut red blue paid
  refine ⟨T,⟨zero,⟨(show F.G ≃g F.G from RelIso.refl _)⟩,rk,ed,ord,head.trans ni,other.trans mj,?_,energy,width⟩,ap⟩
  exact maximum_tail_diagonal F.n F.m F.hn F.hm i j cut red blue

/-- Either orientation of a full head opposite two can be studied
at the actual unshifted row. Reapply the region test on that source,
which may have shorter lists. -/
theorem strict_full_binary_zero_entry (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (binary : let D := diagonal F.n F.m (F.r+2)-1
              (F.n ⟨0,F.hs⟩=D ∧ F.m ⟨0,F.ht⟩=2) ∨ (F.m ⟨0,F.ht⟩=D ∧ F.n ⟨0,F.hs⟩=2)) :
    ∃T:StrictFamily.{u},SamePeakZeroRow F T ∧ AllSmallerPaid.{u} T.rank ∧
      (∀K:DegreeRegion T.G (diagonal T.n T.m (T.r+2)-1),
       let H := T.G.induce K.core
       let D := diagonal T.n T.m (T.r+2)-1
       (T.n ⟨0,T.hs⟩=D → T.t≤matchingEdges H ∧ matchingEdges H<T.s ∧ 0<originalThresholdCount ((componentBudget H T.n).entries T.n) 2) ∧
       (T.m ⟨0,T.ht⟩=D → T.s≤matchingEdges H ∧ matchingEdges H<T.t ∧ 0<originalThresholdCount ((componentBudget H T.m).entries T.m) 2)) := by
  let D := diagonal F.n F.m (F.r+2)-1
  have deg : 5≤D := strict_source_degree_at_least_five F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  change (F.n ⟨0,F.hs⟩=D ∧ F.m ⟨0,F.ht⟩=2) ∨ (F.m ⟨0,F.ht⟩=D ∧ F.n ⟨0,F.hs⟩=2) at binary
  have peak : diagonal F.n F.m (F.r+2)=F.n ⟨0,F.hs⟩+F.m ⟨0,F.ht⟩-1 := by rcases binary with h|h <;> omega
  obtain ⟨T,same,other⟩ := strict_maximum_plateau_zero_entry F paid peak
  refine ⟨T,same,other,?_⟩
  obtain ⟨zero,_,_,_,_,nh,mh,cols,_,_⟩ := same
  have step := cols 0
  simp only [Nat.add_zero,Nat.zero_add] at step
  have eqD : diagonal T.n T.m (T.r+2)-1=D := by rw [zero];simpa [D] using congrArg (fun x:ℕ => x-1) step
  intro K H DT
  have nonunit := strict_full_binary_nonunit_remaining T other K
  have sizes := strict_full_head_unique_escape T other K
  have heads : (T.n ⟨0,T.hs⟩=DT ∧ T.m ⟨0,T.ht⟩=2) ∨ (T.m ⟨0,T.ht⟩=DT ∧ T.n ⟨0,T.hs⟩=2) := by
    change (T.n ⟨0,T.hs⟩=_ ∧ _) ∨ (T.m ⟨0,T.ht⟩=_ ∧ _)
    change DT=D at eqD
    rw [eqD,nh,mh];exact binary
  constructor
  · intro red
    have b : T.m ⟨0,T.ht⟩=2 := by change DT=D at eqD;rcases heads with h|h <;> omega
    obtain ⟨emb,len,_,_⟩ := sizes.1 red
    change matchingEdges H+_+_+_+1≤T.s at len
    exact ⟨emb,by omega,nonunit.1 red b⟩
  · intro blue
    have b : T.n ⟨0,T.hs⟩=2 := by change DT=D at eqD;rcases heads with h|h <;> omega
    obtain ⟨emb,len,_,_⟩ := sizes.2 blue
    change matchingEdges H+_+_+_+1≤T.t at len
    exact ⟨emb,by omega,nonunit.2 blue b⟩

#print axioms strict_maximum_plateau_zero_entry
#print axioms strict_full_binary_zero_entry
end JSP452Audit.StarHost