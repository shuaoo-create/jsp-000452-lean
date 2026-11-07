import TheDegreeCreditSeparatesAnySufficientlyWideSmallerRow
namespace JSP452Audit.StarHost

theorem gap_two_dominant_mass_cost (D Z N c ρ R b l i L w:ℕ) (G g:ℤ)
    (degree:11≤D) (many:3≤c) (supply:1≤ρ) (size:N=2*Z+c) (roots:c+1≤R+ρ) (rp:0<R)
    (mass:6*((D+1)/2)*(c-1)+c<Z) (credit:4*G+2*(D:ℤ)-4+13*((ρ:ℤ)-1)≤0)
    (allow:l=max (N/5) (R+b)) (cut:i=l-R) (high:Z<L) (width:L≤w+i+l) (nonneg:0≤g)
    (cost:g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ)) :
    let p := (D-1)/2
    p+3≤w ∧ g≤4*((w:ℤ)-p-3) := by
  intro p
  have mul := Nat.mul_le_mul_right (c-1) (show 3*D≤6*((D+1)/2) by omega)
  have lower : 3*D*(c-1)+c<Z := by omega
  have expand := Nat.mul_sub_left_distrib (3*D) c 1
  have prod := mul_nonneg (show (0:ℤ)≤(D:ℤ)-11 by omega) (show (0:ℤ)≤(c:ℤ)-3 by omega)
  have cc : ((c-1:ℕ):ℤ)=(c:ℤ)-1 := by omega
  have heavy : 3*(D:ℤ)*((c:ℤ)-1)+c<Z := by rw [←cc];exact_mod_cast lower
  have linear : 6*(D:ℤ)+33*((c:ℤ)-3)+c<Z := by linarith only [heavy,prod]
  have exactCut : i+R=l := by omega
  have sizeZ : (N:ℤ)=2*Z+c := by exact_mod_cast size
  have rootZ : (c:ℤ)+1≤(R:ℤ)+ρ := by exact_mod_cast roots
  have orderZ : (1:ℤ)≤R := by omega
  have small2 : 3*((N/3:ℕ):ℤ)≤N := by omega
  have small3 : 4*((N/4:ℕ):ℤ)≤N := by omega
  have small4 : 5*((N/5:ℕ):ℤ)≤N := by omega
  have cutZ : (i:ℤ)+R=l := by exact_mod_cast exactCut
  have hZ : (Z:ℤ)+1≤L := by omega
  have wZ : (L:ℤ)≤w+i+l := by exact_mod_cast width
  have cZ : (3:ℤ)≤c := by omega
  have dZ : (11:ℤ)≤D := by omega
  have pZ : 2*(p:ℤ)≤D-1 := by dsimp only [p];omega
  have posZ : (1:ℤ)≤ρ := by omega
  have bZ : (0:ℤ)≤b := by positivity
  have massZ : 6*(D:ℤ)+33*((c:ℤ)-3)+c+1≤Z := by omega
  by_cases low:R+b≤N/5
  · rw [max_eq_left low] at allow
    have charge : 30*g≤120*(w:ℤ)+30*G-8*Z+71*c-150*R-150 := by
      have a : 5*(l:ℤ)≤N := allow ▸ small4
      linarith only [cost,sizeZ,small2,small3,a,cutZ,hZ,wZ,bZ]
    have ceil : g≤4*((w:ℤ)-p-3) := by
      linarith only [charge,massZ,credit,rootZ,orderZ,cZ,dZ,pZ]
    exact ⟨by omega,ceil⟩
  · rw [max_eq_right (by omega : N/5≤R+b)] at allow
    have choice : (l:ℤ)=R+b := by exact_mod_cast allow
    have charge : 6*g≤9*(w:ℤ)+6*G-Z+7*c-9*R-15 := by
      linarith only [cost,sizeZ,small2,small3,choice,cutZ,hZ,wZ]
    have ceil : 2*g≤3*((w:ℤ)-p-3) := by
      linarith only [charge,massZ,credit,rootZ,orderZ,cZ,dZ,pZ,posZ]
    exact ⟨by omega,by omega⟩

#print axioms gap_two_dominant_mass_cost
end JSP452Audit.StarHost