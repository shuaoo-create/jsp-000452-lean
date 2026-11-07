import ActualNineDegreeCutCertificate
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem optimal_nine_cut_exists {X:Type u} [Finite X] (G:SimpleGraph X) :
    ∃K:NineOriginalCut G,(∀J:NineOriginalCut G,J.eta≤K.eta) ∧
      ∀J:NineOriginalCut G,J.eta=K.eta → J.S.ncard+J.T.ncard≤K.S.ncard+K.T.ncard := by
  classical
  let _ := Fintype.ofFinite (Set X × Set X)
  let legal := (Finset.univ:Finset (Set X × Set X)).filter (fun p => Disjoint p.1 p.2)
  let score (p:Set X × Set X) := originalFactorCut G 3 6 p.1 p.2
  have check (J:NineOriginalCut G) : (J.S,J.T)∈legal := Finset.mem_filter.mpr ⟨Finset.mem_univ _,J.apart⟩
  let empty : NineOriginalCut G := ⟨∅,∅,by simp⟩
  obtain ⟨a,mem,best⟩ := Finset.exists_max_image legal score ⟨_,check empty⟩
  let tied := legal.filter (fun p => score p=score a)
  obtain ⟨b,chosen,largest⟩ := Finset.exists_max_image tied (fun p => p.1.ncard+p.2.ncard) ⟨a,Finset.mem_filter.mpr ⟨mem,rfl⟩⟩
  obtain ⟨legalB,eq⟩ := Finset.mem_filter.mp chosen
  let K : NineOriginalCut G := ⟨b.1,b.2,(Finset.mem_filter.mp legalB).2⟩
  refine ⟨K,?_,?_⟩
  · intro J;exact (best _ (check J)).trans_eq eq.symm
  · intro J h
    exact largest (J.S,J.T) (Finset.mem_filter.mpr ⟨check J,h.trans eq⟩)

theorem strict_nine_maximal_cut (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    ∃K:NineOriginalCut F.G,
      (highestWidth F.n F.m F.r:ℤ)≤K.eta ∧ K.eta≤2 ∧ K.S.ncard=K.T.ncard+1 ∧
      K.eta+2≤(minimumExposure F.G 9:ℤ) ∧
      (∀J:NineOriginalCut F.G,J.eta≤K.eta) ∧
      ∀J:NineOriginalCut F.G,J.eta=K.eta → J.S.ncard+J.T.ncard≤K.S.ncard+K.T.ncard := by
  obtain ⟨hp,_,_,few,i,j,u,v,_,pair,up,vp,width,force⟩ := strict_nine_original_peak F paid nine
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have lower : ∃J:NineOriginalCut F.G,(highestWidth F.n F.m F.r:ℤ)≤J.eta := by
    rcases pair with ⟨red,blue⟩|⟨red,blue⟩ <;> rw [red,blue] at force
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 7 u v (by decide) (by decide) up vp cap force
      exact ⟨⟨S,T,dis⟩,width ▸ fee⟩
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 7 v u (by decide) (by decide) vp up cap (forces_swap force)
      rw [Nat.add_comm v u,width] at fee;exact ⟨⟨S,T,dis⟩,fee⟩
  obtain ⟨J,fee⟩ := lower
  obtain ⟨K,maximal,roots⟩ := optimal_nine_cut_exists F.G
  have pay := fee.trans (maximal J)
  obtain ⟨gap,exp⟩ := K.actual_root_gap cap few (by omega)
  exact ⟨K,pay,by omega,gap,exp,maximal,roots⟩

#print axioms optimal_nine_cut_exists
#print axioms strict_nine_maximal_cut
end JSP452Audit.StarHost
