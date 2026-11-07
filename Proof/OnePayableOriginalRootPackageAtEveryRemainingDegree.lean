import TheTwoEvenCasesPayTheRootCostOnActualWholeCores
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_high_payable_original_package (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    ∃(K:DegreeRegion F.G D) (k c:ℕ) (P:ScaledPortPlan K k c),0<k ∧ Nonempty (PortGraphLayers P) ∧
      1≤h ∧ h≤P.excess ∧ 4*P.gamma h+((D:ℤ)+1)*P.excess+2*P.beta≤0 ∧
      (D%2=1 → h+1≤P.excess ∧ 4*P.gamma h+((D:ℤ)+3)*P.excess+((D:ℤ)-5)*h+2*P.beta≤0) := by
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
    refine ⟨K,q,p-1,P,by omega,⟨E⟩,pos,by omega,?_,fun _ => ⟨big,by push_cast;exact sharp⟩⟩
    have nonneg : (0:ℤ)≤((p:ℤ)+q-5)*h := mul_nonneg (by omega) (by positivity)
    push_cast;linarith only [sharp,nonneg,show (0:ℤ)≤P.excess by positivity]
  · obtain ⟨op,oq,le⟩ := even (by omega)
    by_cases equal:p=q
    · subst q
      obtain ⟨P⟩ := scaled_port_plan_exists K 1 (K.pieces.ncard+1) (by decide) localCap
      obtain ⟨E⟩ := P.graph_layers
      obtain ⟨_,big,sharp⟩ := central_even_package_exact_credit K P E (by omega) localCap S T apart need
      exact ⟨K,1,_,P,by decide,⟨E⟩,pos,big,by push_cast;exact sharp,fun falseH => (isOdd falseH).elim⟩
    · obtain ⟨P⟩ := scaled_port_plan_exists K (q-p) (p-1) (by omega) localCap
      obtain ⟨E⟩ := P.graph_layers
      obtain ⟨_,big,sharp⟩ := unequal_even_package_exact_credit K P E (Nat.even_iff.mpr (by omega)) (Nat.odd_iff.mpr op)
        (by omega) (by omega) localCap S T apart need
      refine ⟨K,q-p,p-1,P,by omega,⟨E⟩,pos,big,?_,fun falseH => (isOdd falseH).elim⟩
      have nonneg : (0:ℤ)≤((p:ℤ)+q-6)*h := mul_nonneg (by omega) (by positivity)
      push_cast;linarith only [sharp,nonneg,show (0:ℤ)≤P.excess by positivity]

#print axioms strict_high_payable_original_package
end JSP452Audit.StarHost
