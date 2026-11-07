import TheActualDominantMassPaysBothHighAllowanceChoices
namespace JSP452Audit.StarHost

theorem gap_two_short_middle_cost (D Z N c ρ R b u l i L w e:ℕ) (G g:ℤ)
    (degree:11≤D) (size:N=2*Z+c) (room:11*c≤2*Z) (roots:c+1≤R+ρ) (rp:0<R) (supply:1≤ρ) (holes:e≤ρ)
    (credit:4*G+2*(D:ℤ)-4+13*((ρ:ℤ)-1)≤0)
    (allow:l=max (N/4) (R+u)) (short:R+u≤N/3) (cut:i=l-R)
    (wide:(2:ℤ)*Z+b+1≤(L:ℤ)+(N/4:ℕ)+e+G) (width:L≤w+i+N/3)
    (nonneg:0≤g) (cost:g+Z+l+u+b+1≤G+2*((N/3:ℕ):ℤ)+2*i) :
    let p := (D-2)/2
    p+3≤w ∧ g≤3*((w:ℤ)-p-3) := by
  intro p
  have exactCut : i+R=l := by omega
  have sizeZ : (N:ℤ)=2*Z+c := by exact_mod_cast size
  have rootZ : (c:ℤ)+1≤(R:ℤ)+ρ := by exact_mod_cast roots
  have orderZ : (1:ℤ)≤R := by omega
  have small2 : 3*((N/3:ℕ):ℤ)≤N := by omega
  have small3 : 4*((N/4:ℕ):ℤ)≤N := by omega
  have cutZ : (i:ℤ)+R=l := by exact_mod_cast exactCut
  have wZ : (L:ℤ)≤w+i+(N/3:ℕ) := by exact_mod_cast width
  have dZ : (11:ℤ)≤D := by omega
  have pZ : 2*(p:ℤ)≤D-2 := by dsimp only [p];omega
  have posZ : (1:ℤ)≤ρ := by omega
  have bZ : (0:ℤ)≤b := by positivity
  have uZ : (0:ℤ)≤u := by positivity
  have eZ : (e:ℤ)≤ρ := by exact_mod_cast holes
  have charge : 12*g≤36*(w:ℤ)+48*G-2*Z+41*c-48*R+36*e-48 := by
    by_cases low:R+u≤N/4
    · rw [max_eq_left low] at allow
      have a : 4*(l:ℤ)≤N := allow ▸ small3
      linarith only [wide,wZ,cost,cutZ,small2,small3,a,sizeZ,orderZ,uZ,bZ]
    · rw [max_eq_right (by omega : N/4≤R+u)] at allow
      have eq : (l:ℤ)=R+u := by exact_mod_cast allow
      have a : 3*(l:ℤ)≤N := by omega
      linarith only [wide,wZ,cost,cutZ,small2,small3,a,sizeZ,eq,bZ]
  have fee : g≤3*((w:ℤ)-p-3) := by
    by_contra! bad
    have off : 3*((w:ℤ)-p-3)+1≤g := by omega
    have rescue : (Z:ℤ)≤12 := by linarith only [off,charge,credit,pZ,dZ,eZ,posZ,rootZ,orderZ]
    have zsmall : Z≤12 := by omega
    have csmall : c≤2 := by omega
    have rsmall : ρ=1 := by
      by_contra! no
      have rho2 : (2:ℤ)≤ρ := by omega
      linarith only [off,charge,credit,pZ,dZ,eZ,rho2,rootZ,orderZ,show (0:ℤ)≤Z by positivity]
    have exceptional : D≤14 := by
      have zero : (0:ℤ)≤Z := by positivity
      linarith only [off,charge,credit,pZ,eZ,posZ,rootZ,orderZ,zero]
    clear charge off rescue small2 small3 sizeZ orderZ rootZ cutZ dZ pZ posZ bZ uZ eZ wZ
    subst ρ
    dsimp only [p] at bad
    interval_cases Z <;> interval_cases c <;> subst N <;> norm_num at * <;> omega
  exact ⟨by omega,fee⟩

#print axioms gap_two_short_middle_cost
end JSP452Audit.StarHost