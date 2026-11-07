import OnlyOriginalHeadGapsOneAndTwoRemainForTheOfficialEquation
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_original_credit_and_singleton (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    ∃(K:DegreeRegion F.G D) (k c:ℕ) (P:ScaledPortPlan K k c),0<k ∧ Nonempty (PortGraphLayers P) ∧
      1≤h ∧ h≤P.excess ∧ 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 ∧
      (D%2=1 → h+1≤P.excess ∧ 4*P.gamma h+((D:ℤ)+3)*P.excess+((D:ℤ)-5)*h+2*P.beta≤0) ∧
      (P.excess=1 → D%2=0 ∧ h=1 ∧ (oddRegularComponents F.G D).ncard=1 ∧ P.shortfall=0) := by
  intro D h
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤D := (minimal_rank_exact_source F paid).2.2.2.1 v
  obtain ⟨p,q,lp,lq,deg,peak,odd,even,_⟩ := strict_oriented_high_peak F paid
  change p+q=D at deg
  obtain ⟨u,v,up,vp,eq,_,S,T,apart,need⟩ := peak
  change u+v-1=h at eq
  change (h:ℤ)≤originalFactorCut F.G p q S T at need
  have pos : 1≤h := by omega
  have localCap (v:F.X) : Nat.card (F.G.neighborSet v)≤p+q := (cap v).trans_eq deg.symm
  obtain ⟨K⟩ := degreeRegion_exists F.G (p+q)
  rw [←deg]
  by_cases isOdd:(p+q)%2=1
  · obtain ⟨op,oq⟩ := odd (by omega)
    have hp : 3≤p := by omega
    obtain ⟨P⟩ := scaled_port_plan_exists K q (p-1) (by omega) localCap
    obtain ⟨E⟩ := P.graph_layers
    obtain ⟨_,big,sharp⟩ := odd_package_exact_credit K P E (Nat.odd_iff.mpr isOdd) (Nat.odd_iff.mpr op) (by omega) pos
      (by omega) localCap S T apart need
    refine ⟨K,q,p-1,P,by omega,⟨E⟩,pos,by omega,?_,fun _ => ⟨big,by push_cast;exact sharp⟩,fun one => by omega⟩
    push_cast;linarith only [sharp,show (0:ℤ)≤P.excess by positivity,show (0:ℤ)≤h by positivity]
  · obtain ⟨op,oq,le⟩ := even (by omega)
    by_cases equal:p=q
    · subst q
      obtain ⟨P⟩ := scaled_port_plan_exists K 1 (K.pieces.ncard+1) (by decide) localCap
      obtain ⟨E⟩ := P.graph_layers
      obtain ⟨zero,big,_⟩ := central_even_package_exact_credit K P E (by omega) localCap S T apart need
      refine ⟨K,1,_,P,by decide,⟨E⟩,pos,big,?_,fun falseH => (isOdd falseH).elim,?_⟩
      · have hand := (P.exact_weight_and_root_cost E localCap h).2.1
        rw [zero] at hand;push_cast at hand ⊢
        have gain := mul_nonneg (show (0:ℤ)≤(p:ℤ)+p-2 by omega) (show (0:ℤ)≤(P.excess:ℤ)-h by omega)
        linarith only [gain,hand]
      · intro one
        have ct := balanced_cut_le_original_odd_regular F.G p (fun v => (localCap v).trans_eq (by omega)) S T apart
        rw [show 2*p=p+p by omega] at ct
        have reg := P.includes_odd_regular_excess (by decide) E
        exact ⟨by omega,by omega,by omega,zero⟩
    · obtain ⟨P⟩ := scaled_port_plan_exists K (q-p) (p-1) (by omega) localCap
      obtain ⟨E⟩ := P.graph_layers
      obtain ⟨bill,big,sharp⟩ := unequal_even_package_exact_credit K P E (Nat.even_iff.mpr (by omega)) (Nat.odd_iff.mpr op)
        (by omega) (by omega) localCap S T apart need
      refine ⟨K,q-p,p-1,P,by omega,⟨E⟩,pos,big,by push_cast;exact sharp,fun falseH => (isOdd falseH).elim,?_⟩
      intro single
      have eqH : h=1 := by omega
      have upper := P.includes_odd_regular_excess (by omega) E
      rw [single,eqH,Nat.mul_one,Nat.mul_one] at bill
      have reg : (oddRegularComponents F.G (p+q)).ncard=1 := by
        by_contra! none
        rw [show (oddRegularComponents F.G (p+q)).ncard=0 by omega,Nat.mul_zero] at bill;omega
      rw [reg,Nat.mul_one] at bill
      have short := Nat.mul_le_mul_right P.shortfall (show 1≤p-1 by omega)
      exact ⟨by omega,eqH,reg,by omega⟩

#print axioms strict_original_credit_and_singleton
end JSP452Audit.StarHost
