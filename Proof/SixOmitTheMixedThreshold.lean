import OriginalFromSevenDoubleEscape
namespace JSP452Audit.StarHost

theorem six_full_single_numerical (b μ a r d h ρ X Y t q η V K ζ : ℕ)
    (opp : b=2 ∨ b=3) (width : 1≤h ∧ h≤ρ) (res : ρ+1≤d)
    (rank : q+t=μ+1) (space : d+2*Y≤q) (endpoint : a+r+2*(d+X)≤t)
    (vx : 2≤X) (vy : (b-1)/2≤Y) (volume : μ≤3*V+a+ρ)
    (slot : 6*ρ+ζ≤6*V) (root : ζ≤6*a) (rootcap : 6*ρ+ζ+2≤2*h+24)
    (supp : 5*η≤2*(2*μ+a+ρ)) (base : a+q+r≤K) (save : μ+1≤K+η) :
    ζ+2*h+2*d+2*(X+(r+h))≤6*ρ+2*(6-b-1)*K+2*V := by
  obtain ⟨hp,wh⟩ := width
  rcases opp with x|x <;> subst b <;> norm_num at vy ⊢ <;>
    linarith only [hp,wh,res,rank,space,endpoint,vx,vy,volume,slot,root,rootcap,supp,base,save,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]

theorem three_five_half_charge {s : ℕ} (n : Fin s→ℕ) :
    originalThresholdCount n 3+originalThresholdCount n 5≤∑i,(n i-1)/2 := by
  classical
  have each (i:Fin s) : (if 3≤n i then 1 else 0)+(if 5≤n i then 1 else 0)≤(n i-1)/2 := by split_ifs <;> omega
  have all := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i)
  simpa [originalThresholdCount,Finset.sum_add_distrib,Finset.sum_boole] using all

theorem six_omit_actual_mix_mass {s : ℕ} (n : Fin s→ℕ) (j:ℕ) (pos : 3≤j) (cap : j≤4) :
    (∑z∈Finset.range (6-2),if z+3=j then 0 else originalThresholdCount n (z+3))≤
      (∑i,(n i-1)/2)+originalThresholdCount n 6 := by
  have price := three_five_half_charge n
  have smaller := threshold_anti_height n (by decide : 3≤4)
  rcases (show j=3 ∨ j=4 by omega) with x|x <;> subst j <;> simp [Finset.sum_range_succ] <;> omega

#print axioms six_full_single_numerical
#print axioms three_five_half_charge
#print axioms six_omit_actual_mix_mass
end JSP452Audit.StarHost