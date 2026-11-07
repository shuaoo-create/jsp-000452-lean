import OriginalHighDegreeDoubleEscape
import Mathlib.Tactic.IntervalCases
namespace JSP452Audit.StarHost

set_option maxHeartbeats 1500000 in
/-- Each concrete pair uses the actual degree-dependent choice of
suppression size and the actual upper bound for the same root shortfall. -/
theorem finite_full_single_numerical (D b μ a r d h ρ X Y t q η V K ζ : ℕ)
    (degree : 7≤D ∧ D≤14) (opp : 2≤b ∧ 2*b≤D) (width : 1≤h ∧ h≤ρ) (res : ρ+1≤d)
    (inner : q+t=μ+1) (space : d+2*Y≤q) (endpoint : a+r+2*(d+X)≤t)
    (vx : (D-1)/2≤X) (vy : (b-1)/2≤Y) (volume : μ≤3*V+a+ρ)
    (slot : D*ρ+ζ≤D*V) (root : ζ≤D*a) (rootcap : D*ρ+ζ+2≤2*h+2*(D/2)*(D/2+1))
    (p7 : D=7 → 25*η≤9*(2*μ+a+ρ)) (p8 : D=8 → 3*η≤2*μ+a+ρ) (p9 : 9≤D → 13*η≤4*(2*μ+a+ρ))
    (base : a+q+r≤K) (save : μ+1≤K+η) :
    ζ+2*h+2*d+4*X≤D*ρ+2*(D-b-1)*K+2*V := by
  obtain ⟨small,large⟩ := degree
  obtain ⟨bottom,bound⟩ := opp
  have ub : b≤7 := by omega
  obtain ⟨hp,wρ⟩ := width
  interval_cases D
  · have supp := p7 rfl
    have lc : 6≤2*(7-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · by_cases largeB : b=4
    · have supp := p8 rfl
      have lc : 6≤2*(8-b-1) := by omega
      have scale := Nat.mul_le_mul_right K lc
      have yl : 1≤Y := by omega
      norm_num at vx rootcap
      linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
        Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
    · have supp := p8 rfl
      have lc : 8≤2*(8-b-1) := by omega
      have scale := Nat.mul_le_mul_right K lc
      have yl : 0≤Y := by omega
      norm_num at vx rootcap
      linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
        Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 8≤2*(9-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 8≤2*(10-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 10≤2*(11-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 10≤2*(12-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 12≤2*(13-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]
  · have supp := p9 (by decide)
    have lc : 12≤2*(14-b-1) := by omega
    have scale := Nat.mul_le_mul_right K lc
    have yl : 0≤Y := by omega
    norm_num at vx rootcap
    linarith only [hp,wρ,res,inner,space,endpoint,vx,yl,volume,slot,root,rootcap,supp,base,save,scale,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le ρ,Nat.zero_le V,Nat.zero_le η,Nat.zero_le K,Nat.zero_le ζ]

#print axioms finite_full_single_numerical
end JSP452Audit.StarHost